//*  -*- mode: c; indent-tabs-mode: nil; c-basic-offset: 4; tab-width: 8; -*- */

/* TO-DO:
 *
 */

/*
 * Copyright (c) 2006-2009,2013,2014 Genome Research Ltd (GRL).
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials
 *       provided with the distribution.
 *
 *     * Neither the name of the Genome Research Limited nor the
 *       names of its contributors may be used to endorse or promote
 *       products derived from this software without specific prior
 *       written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY GRL ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL GRL BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 */

/*
 * Author: Martin Pollard, 2013, 2014 *
 * This code looks for spatial features given an aligned bam file
 *
 */

#ifdef HAVE_CONFIG_H
#include "pb_config.h"
#endif

#define _GNU_SOURCE // for asprintf

#include <stdbool.h>
#include <stdio.h>
#include <errno.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <ctype.h>
#include <fcntl.h>
#include <math.h>
#include <assert.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <stdarg.h>
#include <getopt.h>
#include <png.h>

#include <rTreeIndex.h>


/* To turn off assert for a small speed gain, uncomment this line */
/* #define NDEBUG */

/* Hack to stop io_lib from trying to include its own config.h */
#ifdef HAVE_CONFIG_H
#undef HAVE_CONFIG_H
#endif
#include <io_lib/misc.h>
#include <io_lib/hash_table.h>

#include <sam.h>

#include <smalloc.h>
#include <aprintf.h>
#include <die.h>
#include <rts.h>
#include <shared.h>
#include <snp.h>
#include <parse_bam.h>

#include "shared/version.h"

#define PHRED_QUAL_OFFSET  33  // phred quality values offset

#define REGION_MIN_COUNT            122    // minimum coverage when setting region state

// assuming a region size of 700 and ~125 reads in a region, a threshold of 0.016 equates to 2 reads in a region
#define REGION_MISMATCH_THRESHOLD   0.016  // threshold for setting region mismatch state
#define REGION_INSERTION_THRESHOLD  0.016  // threshold for setting region insertion state
#define REGION_DELETION_THRESHOLD   0.016  // threshold for setting region deletion state

#define TILE_REGION_THRESHOLD  0.75  // threshold for setting region state at tile level

#define REGION_STATE_MASK  (REGION_STATE_INSERTION | REGION_STATE_DELETION)  // region mask used to filter reads

#define READ_LEN 100

typedef struct {
	char *cmdline;
	char *snp_file;
	char *in_bam_file;
	HashTable *snp_hash;
	char *working_dir;
	char *output;
	int read_length[N_READS];
	bool calculate_i;
	bool calculate_ii;
	bool apply;
	bool qcfail;
	bool quiet;
	int surface;
	int read;
	int min_cycle_idx;
	int max_cycle_idx;
	int compress;
	bool dump_label_image;
} Settings;


/*
 * Generates two pictures per tile per cycle
 * INDEL binary picture
 * MISMATCH binary picture
 *
 * known SNPs are ignored
 * binary picture is an indexed PNG with 1-bit per pixel of bit-depth
 */

typedef struct TileImage {
	FILE* file_ptr;
	png_structp png;
	png_infop png_header;
	png_infop png_footer;
	png_bytepp bitmap;
} TileImage_t;

#define DOWNSAMPLE_AMOUNT 4
static const int X_LEN = (2048*3+100)/DOWNSAMPLE_AMOUNT;
static const int Y_LEN = (10000*16+100)/DOWNSAMPLE_AMOUNT;

#define ROWBINARYSET(x,y,value_array) value_array[y/DOWNSAMPLE_AMOUNT][x/(8*DOWNSAMPLE_AMOUNT)]|=128>>(x/DOWNSAMPLE_AMOUNT)%8

static TileImage_t* create_image(TileImage_t* existing, const char* prefix, const char* ftype, int surface, int read, int cycle)
{
	char buf_png[255];
	sprintf(buf_png, "%s_%s_%d_%d_%d.png", prefix, ftype, surface, read, cycle);
	fprintf(stderr, "image name (%s)\n", buf_png);


	TileImage_t* img;
	if (existing == NULL)
		img = (TileImage_t*)malloc(sizeof(TileImage_t));
	else
		img = existing;
	
	img->png = png_create_write_struct
	(PNG_LIBPNG_VER_STRING, NULL, NULL, NULL);
	if (!img->png)
	{
		if (!existing) free(img);
		fprintf(stderr, "create_image: cannot allocate png write struct\n");
		return NULL;
	}
	
	img->png_header = png_create_info_struct(img->png);
	if (!img->png_header)
	{
		png_destroy_write_struct(&img->png,
								 (png_infopp)NULL);
		if (!existing) free(img);
		fprintf(stderr, "create_image: cannot allocate png info struct\n");
		return NULL;
	}

	img->file_ptr = fopen(buf_png, "wb");
	if (!img->file_ptr)
	{
		png_destroy_write_struct(&img->png,
								 &img->png_header);
		if (!existing) free(img);
		fprintf(stderr, "create_image: cannot open file to write to\n");
		perror("");
		return NULL;
	}

	png_set_IHDR(img->png, img->png_header, X_LEN, Y_LEN, 1, PNG_COLOR_TYPE_GRAY, PNG_INTERLACE_NONE, PNG_COMPRESSION_TYPE_DEFAULT, PNG_FILTER_TYPE_DEFAULT);
	img->bitmap = (png_bytepp)png_malloc(img->png, Y_LEN * sizeof(png_bytep));

	if (!img->bitmap)
	{
		png_destroy_write_struct(&img->png,
								 &img->png_header);
		fclose(img->file_ptr);
		if (!existing) free(img);
		fprintf(stderr, "create_image: Cannot allocate memory for bitmap y.\n");
		return NULL;
	}
	
	int i;
	for (i = 0; i < Y_LEN; ++i) {
		img->bitmap[i] = (png_bytep)png_malloc(img->png, png_get_rowbytes(img->png,img->png_header));
		if (!img->bitmap[i])
		{
			png_destroy_write_struct(&img->png,
									 &img->png_header);
			fclose(img->file_ptr);
			free(img->bitmap);
			if (!existing) free(img);
			fprintf(stderr, "create_image: Cannot allocate memory for bitmap x.\n");
			return NULL;
		}
		memset(img->bitmap[i], 0, png_get_rowbytes(img->png,img->png_header));
	}
	return img;
}

/// HAAAAAACK!
static TileImage_t* create_gray_image(TileImage_t* existing, const char* prefix, const char* ftype, int surface, int read, int cycle)
{
	char buf_png[255];
	sprintf(buf_png, "%s_%s_%d_%d_%d.png", prefix, ftype, surface, read, cycle);
	fprintf(stderr, "image name (%s)\n", buf_png);
	
	
	TileImage_t* img;
	if (existing == NULL)
		img = (TileImage_t*)malloc(sizeof(TileImage_t));
	else
		img = existing;
	
	img->png = png_create_write_struct
	(PNG_LIBPNG_VER_STRING, NULL, NULL, NULL);
	if (!img->png)
	{
		if (!existing) free(img);
		return NULL;
	}
	
	img->png_header = png_create_info_struct(img->png);
	if (!img->png_header)
	{
		png_destroy_write_struct(&img->png,
								 (png_infopp)NULL);
		if (!existing) free(img);
		return NULL;
	}
	
	img->file_ptr = fopen(buf_png, "wb");
	if (!img->file_ptr)
	{
		png_destroy_write_struct(&img->png,
								 &img->png_header);
		if (!existing) free(img);
		return NULL;
	}
	
	png_set_IHDR(img->png, img->png_header, X_LEN, Y_LEN, 8, PNG_COLOR_TYPE_GRAY, PNG_INTERLACE_NONE, PNG_COMPRESSION_TYPE_DEFAULT, PNG_FILTER_TYPE_DEFAULT);
	img->bitmap = (png_bytepp)png_malloc(img->png, Y_LEN * sizeof(png_bytep));
	
	if (!img->bitmap)
	{
		png_destroy_write_struct(&img->png,
								 &img->png_header);
		fclose(img->file_ptr);
		if (!existing) free(img);
		return NULL;
	}
	
	int i;
	for (i = 0; i < Y_LEN; ++i) {
		img->bitmap[i] = (png_bytep)png_malloc(img->png, png_get_rowbytes(img->png,img->png_header));
		if (!img->bitmap[i])
		{
			png_destroy_write_struct(&img->png,
									 &img->png_header);
			fclose(img->file_ptr);
			free(img->bitmap);
			if (!existing) free(img);
			return NULL;
		}
		memset(img->bitmap[i], 0, png_get_rowbytes(img->png,img->png_header));
	}
	return img;
}

static void write_close_image(TileImage_t* img)
{
	png_init_io(img->png, img->file_ptr);
	png_write_info(img->png, img->png_header);
	png_write_image(img->png, img->bitmap);
	png_write_end(img->png, img->png_header);
	
	int i;
	for (i = 0; i < Y_LEN; ++i) {
		png_free(img->png, img->bitmap[i]);
	}
	png_free(img->png, img->bitmap);
	
	png_destroy_write_struct(&img->png, &img->png_header);
	fclose(img->file_ptr);
}

static void nowrite_close_image(TileImage_t* img)
{
	int i;
	for (i = 0; i < Y_LEN; ++i) {
		png_free(img->png, img->bitmap[i]);
	}
	png_free(img->png, img->bitmap);
	
	png_destroy_write_struct(&img->png, &img->png_header);
	fclose(img->file_ptr);
}


static bool update_surface_cycle_image(Settings *s, TileImage_t** row_mismatch_image, TileImage_t** row_indel_image, int read, int x, int y, int *read_mismatch) {
	int cycle;

	for (cycle = 0; cycle < s->read_length[read]; cycle++) {
		if (read_mismatch[cycle] & (BASE_INSERTION|BASE_DELETION)) {
			ROWBINARYSET(x,y,row_indel_image[read][cycle].bitmap);
		} else if (!(read_mismatch[cycle]&BASE_KNOWN_SNP) && (read_mismatch[cycle] & BASE_MISMATCH) ){
			ROWBINARYSET(x,y,row_mismatch_image[read][cycle].bitmap);
		}
	}
	return true;
}

/*
 * Takes the bam file as input and creates images representing the tiles
 *
 * Assumption: within a single input file, all reads are the same length and
 * we're using unclipped data.
 *
 * Returns: 0 written for success
 *	   -1 for failure
 */
static const int N_SURFACES = 2;

static void make_tile_images(Settings *s, samfile_t *fp_bam, TileImage_t* tile_img_mismatch[N_SURFACES][(N_READS-1)], TileImage_t* tile_img_indel[N_SURFACES][(N_READS-1)], int *ntiles, size_t * nreads)
{
	int lane = -1;

	size_t nreads_bam = 0;

	static const int bam_read_buff_size = 1024;
	char bam_read_seq[bam_read_buff_size];
	int bam_read_qual[bam_read_buff_size];
	int bam_read_mismatch[bam_read_buff_size];

	bam1_t *bam = bam_init1();

	int isurface, iread, icycle;
	
	fprintf(stderr, "entering image init loop\n");
	for(isurface=0;isurface < N_SURFACES; ++isurface) {
		fprintf(stderr, "entering image init loop surface %d\n", isurface);
		for(iread=0; iread < (N_READS-1); ++iread) {
			fprintf(stderr, "entering image init loop read %d, s->read_length %d\n", iread, s->read_length[iread]);
			s->read_length[iread] = READ_LEN; // HACK!
			tile_img_mismatch[isurface][iread] = calloc(s->read_length[iread], sizeof(TileImage_t));
			tile_img_indel[isurface][iread] = calloc(s->read_length[iread], sizeof(TileImage_t));
			for(icycle=0; icycle < s->read_length[iread]; ++icycle) {
				fprintf(stderr, "trace: setting up image: surface %d, read %d, cycle %d\n", isurface, iread, icycle);
				if (create_image(&tile_img_mismatch[isurface][iread][icycle], s->output, "mm", isurface, iread, icycle) == NULL) die("ERROR: allocating image memory surface %i read %i cycle %i.\n", isurface, iread, icycle);
				if (create_image(&tile_img_indel[isurface][iread][icycle], s->output, "id", isurface, iread, icycle) == NULL) die("ERROR: allocating image memory surface %i read %i cycle %i.\n", isurface, iread, icycle);
			}
		}
	}

	fprintf(stderr, "entering bam read loop\n");

	/* loop over reads in the bam file */
	while (1) {
		int bam_lane = -1, bam_tile = -1, bam_read = -1, bam_x = -1, bam_y = -1, read_length;

		if (parse_bam_readinfo(fp_bam, bam, &bam_lane, &bam_tile, &bam_x, &bam_y, &bam_read, NULL)) {
			break;	/* break on end of BAM file */
		}

		if (BAM_FUNMAP & bam->core.flag) continue;
		if (BAM_FQCFAIL & bam->core.flag) continue;
		if (BAM_FPAIRED & bam->core.flag) {
			if (0 == (BAM_FPROPER_PAIR & bam->core.flag)) {
				continue;
			}
		}

		parse_bam_alignments(fp_bam, bam, bam_read_seq, bam_read_qual, NULL, bam_read_mismatch,
							 bam_read_buff_size, s->snp_hash);
		char parseTile[10];
		snprintf(parseTile, 10, "%d", bam_tile);
		int surface = parseTile[0] - '1';
		int swath = parseTile[1] - '1';
		int tile = atoi(parseTile+2)-1;
		bam_x += (swath*20480); // FIXME: get these two constants from settings?
		bam_y += (tile*100000);
		bam_x /= 10;
		bam_y /= 10;

		read_length = strlen(bam_read_seq);
		if (0 == s->read_length[bam_read]) {
			s->read_length[bam_read] = read_length;
		}

		if (s->read_length[bam_read] != read_length) {
			die("Error: inconsistent read lengths within bam file for read %d.\nHave length %ld, previously it was %d.\n",
			    bam_read, (long)read_length,
			    s->read_length[bam_read]);
		}

		if (lane == -1) {
			lane = bam_lane;
		}
		if (bam_lane != lane) {
			die("Error: Inconsistent lane within bam file.\nHave %d, previously it was %d.\n", bam_lane, lane);
		}

		if (!update_surface_cycle_image(s, tile_img_mismatch[surface], tile_img_indel[surface], (bam_read-1), bam_x, bam_y, bam_read_mismatch)) {
			die("ERROR: updating image values for surface %i.\n", surface);
		}
		nreads_bam++;
	}

	bam_destroy1(bam);
	
	for(isurface=0;isurface<N_SURFACES; ++isurface) {
		for(iread=0; iread<(N_READS-1); ++iread) {
			for(icycle=0; icycle < s->read_length[iread]; ++icycle) {
				write_close_image(&tile_img_mismatch[isurface][iread][icycle]);
				write_close_image(&tile_img_indel[isurface][iread][icycle]);
			}
		}
	}

	*nreads = nreads_bam;
}

#define PRECISION 0.6
static double** make_gaussian(double sigma, size_t * n_out)
{
	size_t n = ceil(sigma*sqrt(-2.0*log(PRECISION)))+1.0; // determine size based on sigma
	size_t array_size = (n*2 + 1);
	double** retval = malloc(sizeof(double*)*array_size);
	size_t i;
	for (i = 0; i < array_size; ++i) retval[i] = malloc(sizeof(double) * array_size);
	
	// First create matrix
	double divisor = 0;
	double two_sigma_sq = 2.0 * pow(sigma,2);

	int cov_x, cov_y;
	for (cov_y = -((int)n); cov_y <= (int)n; cov_y++) {
		for (cov_x = -((int)n); cov_x <= (int)n; cov_x++) {
			double value = 0.0;
			value = exp(-((pow(cov_x,2.0) / (two_sigma_sq)) + ( pow(cov_y,2.0) / (two_sigma_sq) )  ));
			retval[cov_y+n][cov_x+n] = value;
			divisor += value;
		}
	}
	
	// next normalise it
	int x, y;
	for (y = 0; y < array_size; ++y) {
		for (x = 0; x < array_size; ++x) {
			retval[y][x] /= divisor;
		}
	}
	
	*n_out = n;
	return retval;
}

#define THRESHOLD 245.0

static void apply_gaussian_and_threshold(png_bytepp row_p, png_bytepp output_rows, const int width, const int height, double** kernel, const size_t n)
{
	int x_iter, y_iter;
	for (y_iter = 0; y_iter < height; ++y_iter) {
		for (x_iter= 0; x_iter < width; ++x_iter) {
			// apply convolution to pixel at (x_iter,y_iter)
			double accum = 0;
			int cov_x, cov_y;
			for (cov_y = -(int)n; cov_y <= (int)n; cov_y++) {
				for (cov_x = -(int)n; cov_x <= (int)n; cov_x++) {
					// Get target input coords
					int target_x = x_iter + cov_x;
					int target_y = y_iter + cov_y;
					target_x = target_x >= 0 ? target_x : 0;
					target_y = target_y >= 0 ? target_y : 0;
					target_x = target_x < width ? target_x : width - 1;
					target_y = target_y < height ? target_y : height - 1;
					
					accum += row_p[target_y][target_x] * kernel[cov_y+n][cov_x+n];
				}
			}
			// And threshold
			if (accum < THRESHOLD) {
				output_rows[y_iter][x_iter] = 0;
			} else {
				output_rows[y_iter][x_iter] = 255;
			}
			//output_rows[y_iter][x_iter] = (png_byte)accum;
		}
	}
}

static TileImage_t* read_png_image(const char* fn)
{
	TileImage_t* retval = malloc(sizeof(TileImage_t));
	retval->file_ptr = fopen(fn, "rb");
	if (!retval->file_ptr) {
		free(retval);
		return NULL;
	}

	// Check this is a png
	png_byte buf[8];

	if (fread(&buf, 8, 1, retval->file_ptr) != 1 || png_sig_cmp(buf, 0, 8)) {
		fclose(retval->file_ptr);
		free(retval);
		return NULL;
	}
	
	if ((retval->png = png_create_read_struct(PNG_LIBPNG_VER_STRING, NULL, NULL, NULL)) == NULL) {
		fclose(retval->file_ptr);
		free(retval);
		return NULL;
	}
	
	if ((retval->png_header = png_create_info_struct(retval->png)) == NULL) {
		png_destroy_read_struct(&retval->png, NULL, NULL);
		fclose(retval->file_ptr);
		free(retval);
		return NULL;
	}

	if ((retval->png_footer = png_create_info_struct(retval->png)) == NULL) {
		png_destroy_read_struct(&retval->png, &retval->png_header, NULL);
		fclose(retval->file_ptr);
		free(retval);
		return NULL;
	}

	png_set_sig_bytes(retval->png, 8);  // Mark that we've already done the sigcheck

	png_init_io(retval->png, retval->file_ptr);
	png_set_expand_gray_1_2_4_to_8(retval->png);
	png_read_png(retval->png, retval->png_header, PNG_TRANSFORM_EXPAND|PNG_TRANSFORM_INVERT_MONO, NULL);
	retval->bitmap = png_get_rows(retval->png, retval->png_header);
	
	return retval;
}

typedef struct uf_array
{
	size_t max_uf;
	size_t next_label;
	int* parent;
} uf_array_t;

static void init_uf_array(uf_array_t* array)
{
	array->max_uf = 100;
	array->next_label = 1;
	array->parent = calloc(array->max_uf,sizeof(int));
}

static const int UF_INCREMENT = 100;

static void uf_union(int parent, int child, uf_array_t* uf_array_data)
{
	if (child >= uf_array_data->max_uf) { // if we're bigger than existing array make it bigger
		int from = uf_array_data->max_uf;
		uf_array_data->max_uf += UF_INCREMENT;
		uf_array_data->parent = realloc(uf_array_data->parent, uf_array_data->max_uf*sizeof(int));
		memset(uf_array_data->parent+from, 0, UF_INCREMENT*sizeof(int)); // Zero out new memory
	}
	int j = parent;
	int k = child;
	while (uf_array_data->parent[j] != 0)
		j = uf_array_data->parent[j];
	while (uf_array_data->parent[k] != 0)
		k = uf_array_data->parent[k];
	if (j!=k)
		uf_array_data->parent[k] = j;
}

static int uf_find_inner(int label, uf_array_t* uf_array_data)
{
	if (uf_array_data->parent[label] != 0) {
		// Set node parent to the highest parent in the tree to speed further searchesm
		uf_array_data->parent[label] = uf_find_inner(uf_array_data->parent[label], uf_array_data);
		return uf_array_data->parent[label];
	} else {
		return label;
	}
}

int uf_find(int label, uf_array_t* uf_array_data){
	if ( label >= uf_array_data->max_uf)
		return label;
	
	return uf_find_inner(label, uf_array_data);
}

typedef struct xywh {
	int x; // leftmost coord
	int y; // uppermost coord
	int xw; // x+width
	int yh; // y+height
} xywh_t;

typedef struct xywh_cont {
	size_t n;
	xywh_t* objs;
} xywh_cont_t;

xywh_cont_t* xywh_cont_init(size_t count)
{
	xywh_cont_t* retval = (xywh_cont_t*)malloc(sizeof(xywh_cont_t));
	retval->n = count;
	retval->objs = (xywh_t*)malloc(sizeof(xywh_t) * count);
	return retval;
}

void xywh_cont_free(xywh_cont_t* restrict data)
{
	free(data->objs);
	free(data);
}

size_t fwrite_xywh_cont(const xywh_cont_t* restrict data, FILE* restrict file)
{
	size_t n = fwrite( &data->n, sizeof(size_t), 1, file );
	if (n == 0) return 0;
	size_t o = fwrite( data->objs, sizeof(xywh_t), data->n, file );
	if (o == 0) return 0;
	return n+o;
}

size_t fread_xywh_cont( xywh_cont_t** restrict data, FILE* restrict file)
{
	xywh_cont_t* retval = (xywh_cont_t*)malloc(sizeof(xywh_cont_t));
	size_t n = fread( &retval->n, sizeof(size_t), 1, file );
	if (n == 0){
		free(retval);
		return 0;
	}
	retval->objs = (xywh_t*)malloc(sizeof(xywh_t) * retval->n);
	if (retval->n == 0) {
		*data = retval;
		return n;
	}
	size_t o = fread( retval->objs, sizeof(xywh_t), retval->n, file );
	if (o == 0){
		free(retval->objs);
		free(retval);
		return 0;
	}
	*data = retval;
	return n+o;
}


#ifdef DUMPMAP
static void dumpMap(unsigned char** map, const char* filename)
{
	TileImage_t* img;
	img = (TileImage_t*)malloc(sizeof(TileImage_t));
	
	img->png = png_create_write_struct
	(PNG_LIBPNG_VER_STRING, NULL, NULL, NULL);
	if (!img->png)
	{
		free(img);
		return;
	}
	
	img->png_header = png_create_info_struct(img->png);
	if (!img->png_header)
	{
		png_destroy_write_struct(&img->png,
								 (png_infopp)NULL);
		free(img);
		return;
	}
	
	img->file_ptr = fopen(filename, "wb");
	if (!img->file_ptr)
	{
		png_destroy_write_struct(&img->png,
								 &img->png_header);
		free(img);
		return;
	}
	
	png_init_io(img->png, img->file_ptr);
	png_set_IHDR(img->png, img->png_header, X_LEN, Y_LEN, 8, PNG_COLOR_TYPE_GRAY, PNG_INTERLACE_NONE, PNG_COMPRESSION_TYPE_DEFAULT, PNG_FILTER_TYPE_DEFAULT);
	png_write_info(img->png, img->png_header);
	img->bitmap = map;
	
	png_write_image(img->png, img->bitmap);
	png_write_end(img->png, img->png_header);
	
	int i;
	for (i = 0; i < Y_LEN; ++i) {
		png_free(img->png, img->bitmap[i]);
	}
	png_free(img->png, img->bitmap);
	
	png_destroy_write_struct(&img->png, &img->png_header);
	fclose(img->file_ptr);
}
#endif


/*
 * @returns int[height][width] array of labels corresponding to bitmap
 */
static xywh_cont_t* connected_four(png_bytepp bitmap, const int width, const int height)
{
	// based on: https://en.wikipedia.org/w/index.php?title=Connected-component_labeling&oldid=575300229
	// and http://www.cse.msu.edu/~stockman/Book/2002/Chapters/ch3.pdf
	int x_iter, y_iter;
	const int BACKGROUND_COLOUR = 255;
	unsigned char** label_map = malloc(sizeof(unsigned char*)*height);
	uf_array_t uf_array_data;
	init_uf_array(&uf_array_data);
	
	// First pass: record equiv and assign temp labels
	for (y_iter = 0; y_iter < height; ++y_iter) {
		label_map[y_iter] = calloc(width, sizeof(unsigned char));
		for (x_iter = 0; x_iter < width; ++x_iter) {
			if (bitmap[y_iter][x_iter] == BACKGROUND_COLOUR) continue;  // ignore white pixels
			if (x_iter == 0 || y_iter == 0 ) { // special cases for edges
				if (x_iter == 0 && y_iter == 0 ) {
					label_map[y_iter][x_iter] = uf_array_data.next_label++;
				} else if (x_iter == 0 && bitmap[y_iter][x_iter] == bitmap[y_iter-1][x_iter]) {
					label_map[y_iter][x_iter] = label_map[y_iter][x_iter-1];
				} else if (y_iter == 0 && bitmap[y_iter][x_iter] == bitmap[y_iter-1][x_iter]) {
					label_map[y_iter][x_iter] = label_map[y_iter][x_iter-1];
				} else {
					label_map[y_iter][x_iter] = uf_array_data.next_label++;
				}
			} else {
				if ( bitmap[y_iter][x_iter] == bitmap[y_iter][x_iter-1] // if both have labels
					&& bitmap[y_iter][x_iter] == bitmap[y_iter-1][x_iter] ) {
					if ( label_map[y_iter][x_iter-1] == label_map[y_iter-1][x_iter] ) {
						label_map[y_iter][x_iter] = label_map[y_iter-1][x_iter];
					} else if ( label_map[y_iter][x_iter-1] < label_map[y_iter-1][x_iter] ) {
						label_map[y_iter][x_iter] = label_map[y_iter][x_iter-1];
						uf_union(label_map[y_iter][x_iter],label_map[y_iter-1][x_iter],&uf_array_data);
					}
					else {
						label_map[y_iter][x_iter] = label_map[y_iter-1][x_iter];
						uf_union(label_map[y_iter][x_iter],label_map[y_iter][x_iter-1],&uf_array_data);
					}
				} else if ( bitmap[y_iter][x_iter] != bitmap[y_iter][x_iter-1] // if one does
						    && bitmap[y_iter][x_iter] == bitmap[y_iter-1][x_iter] ) {
					label_map[y_iter][x_iter] = label_map[y_iter-1][x_iter];
				} else if ( bitmap[y_iter][x_iter] == bitmap[y_iter][x_iter-1]
						    && bitmap[y_iter][x_iter] != bitmap[y_iter-1][x_iter] ) {
					label_map[y_iter][x_iter] = label_map[y_iter][x_iter-1];
				} else { // we are a new patch
					label_map[y_iter][x_iter] = uf_array_data.next_label++;
				}
			}
		}
	}

	size_t ml_ii = 0;
	// second pass: replace temp labels by equiv class
	for (y_iter = 0; y_iter < height; ++y_iter) {
		for (x_iter = 0; x_iter < width; ++x_iter) {
			if (bitmap[y_iter][x_iter] == BACKGROUND_COLOUR) continue;  // ignore white pixels
			
			label_map[y_iter][x_iter] = uf_find(label_map[y_iter][x_iter], &uf_array_data);
			ml_ii = label_map[y_iter][x_iter] > ml_ii ? label_map[y_iter][x_iter] : ml_ii;
		}
	}

	int loop_iter;
	int count = 0;
	int* transform_parent = malloc(sizeof(int)*(ml_ii+1));
	for ( loop_iter = 0; loop_iter < ml_ii+1; ++loop_iter ) { if (uf_array_data.parent[loop_iter] == 0) {  transform_parent[loop_iter] = count++; } }
	
	xywh_cont_t* objects = xywh_cont_init(count-1);
	int object_iter;
	// init the structs
	for (object_iter = 0; object_iter < count-1; ++object_iter) {
		xywh_t* this_obj = objects->objs + object_iter;
		this_obj->x = width-1;
		this_obj->y = height-1;
		this_obj->xw = 0;
		this_obj->yh = 0;
	}
	// third pass: reduce labels this should probably be folded into 2nd pass
	for (y_iter = 0; y_iter < height; ++y_iter) {
		for (x_iter = 0; x_iter < width; ++x_iter) {
			int label = transform_parent[label_map[y_iter][x_iter]];
			if (label == 0) continue;
			xywh_t* this_obj = objects->objs + label - 1;
			if ( this_obj->x > x_iter ) this_obj->x = x_iter;
			if ( this_obj->y > y_iter ) this_obj->y = y_iter;
			if ( this_obj->xw < x_iter ) this_obj->xw = x_iter;
			if ( this_obj->yh < y_iter ) this_obj->yh = y_iter;
		}
	}
	// done with this
	for (y_iter = 0; y_iter < height; ++y_iter) {
		free(label_map[y_iter]);
	}
	free(label_map);
// TRACE
	int print_obj_iter;
	printf("dumping object list:\n");
	for (print_obj_iter = 0; print_obj_iter < count-1; ++print_obj_iter)
	{
		xywh_t* this_obj = objects->objs + print_obj_iter;
		printf("%d: (%d,%d)-(%d,%d)\n",print_obj_iter, this_obj->x, this_obj->y, this_obj->xw, this_obj->yh );
	}

	return objects;
}

// Read image file is in variable "image"
static xywh_cont_t* make_filter_image(Settings *s, TileImage_t* image, int surface, int read, int cycle)
{
	// create greyscale image for gaussian
	TileImage_t* outimg = create_gray_image(NULL, s->output, "filter", surface, read, cycle);
	size_t n;

	// Create gaussian kernel matrix (10 pixel radius sigma)
	double** kernel = make_gaussian(10, &n);
	// Perform gaussian convolution and then threshold back to binary
	apply_gaussian_and_threshold(image->bitmap, outimg->bitmap, png_get_image_width(image->png, image->png_header), png_get_image_height(image->png, image->png_header), kernel, n);

	// Detect ROI by 4 connected labelling
	xywh_cont_t* objs = connected_four(outimg->bitmap, png_get_image_width(image->png, image->png_header), png_get_image_height(image->png, image->png_header));
	if (s->dump_label_image) {
		write_close_image(outimg);
	} else {
		nowrite_close_image(outimg);
	}
	return objs;
}

static void make_filter_read(Settings *s, int isurface, int iread)
{
	fprintf(stderr, "entering filter loop read %d, s->read_length %d\n", iread, s->read_length[iread]);
	int icycle;
	
	s->read_length[iread] = READ_LEN; // HACK!
	int min = s->min_cycle_idx != -1 ? s->min_cycle_idx : 0;
	int max = s->read_length[iread];
	if ( s->max_cycle_idx != -1 ) {
		max = s->read_length[iread] < s->max_cycle_idx? s->read_length[iread] : s->max_cycle_idx;
	}
	
	for(icycle=min; icycle < max; ++icycle) {
		// Load images
		char* buf_mm = NULL;
		char* buf_id = NULL;
		asprintf(&buf_mm, "%s_mm_%d_%d_%d.png",s->output, isurface, iread, icycle);
		asprintf(&buf_id, "%s_id_%d_%d_%d.png",s->output, isurface, iread, icycle);
		TileImage_t* image_mm = read_png_image(buf_mm);
		TileImage_t* image_id = read_png_image(buf_id);
		free(buf_mm);
		free(buf_id);

		// Get objects in image
		xywh_cont_t* obj_mm = make_filter_image(s, image_mm, isurface, iread, icycle);
		// Write to file
		char* obj_mm_buf = NULL;
		asprintf(&obj_mm_buf, "%s_mm_%d_%d_%d.obj",s->output, isurface, iread, icycle);
		FILE* obj_mm_file = fopen(obj_mm_buf,"w");
		fwrite_xywh_cont(obj_mm, obj_mm_file);
		fclose(obj_mm_file);
		xywh_cont_free(obj_mm);
		
		// Get objects in image
		xywh_cont_t* obj_id = make_filter_image(s, image_id, isurface, iread, icycle);
		// Write to file
		char* obj_id_buf = NULL;
		asprintf(&obj_id_buf, "%s_id_%d_%d_%d.obj",s->output, isurface, iread, icycle);
		FILE* obj_id_file = fopen(obj_id_buf,"w");
		fwrite_xywh_cont(obj_id, obj_id_file);
		fclose(obj_id_file);
		xywh_cont_free(obj_id);
	}
}

static void make_filter_surface(Settings *s, int isurface)
{
	if (s->read == -1) {
		int iread;
		fprintf(stderr, "entering filter loop surface %d\n", isurface);
		for(iread=0; iread < (N_READS-1); ++iread) {
			make_filter_read(s, isurface, iread);
		}
	} else {
		make_filter_read(s, isurface, s->read);
	}
}

typedef struct rtree_entry {
	int read;
	int idmm;
	int cycle;
} rtree_entry_t;

static void obj_to_rtree(char* output, int idmm, int isurface, int iread, int icycle, struct Node* root[N_SURFACES])
{
	// Read objects from file
	char* obj_mm_buf = NULL;
	xywh_cont_t* obj_mm = NULL;
	asprintf(&obj_mm_buf, "%s_%s_%d_%d_%d.obj", output, idmm == 0 ? "id":"mm", isurface, iread, icycle);
	FILE* obj_mm_file = fopen(obj_mm_buf,"r");
	if ( obj_mm_file == NULL ) { perror("Warning could not open file"); return; }
	if ( fread_xywh_cont(&obj_mm, obj_mm_file) == 0 ) { fprintf(stderr, "Cannot read object from file %s.\n", obj_mm_buf); return; }
	fclose(obj_mm_file);
	free(obj_mm_buf);
	
	// Add to rtree
	int iobjs;
	for (iobjs = 0; iobjs < obj_mm->n; ++iobjs) {
		struct Rect* r = malloc(sizeof(struct Rect));
		r->boundary[0] = obj_mm->objs[iobjs].x;
		r->boundary[1] = obj_mm->objs[iobjs].y;
		r->boundary[2] = obj_mm->objs[iobjs].xw;
		r->boundary[3] = obj_mm->objs[iobjs].yh;

		rtree_entry_t* entry = (rtree_entry_t*)malloc(sizeof(rtree_entry_t));
		entry->read = iread;
		entry->idmm = 1;
		entry->cycle = icycle;
		RTreeInsertRect(r, (int64_t)entry, &root[isurface], 0);
	}
	xywh_cont_free(obj_mm);
}

static void make_rtree_read(Settings* s, int isurface, int iread, struct Node* root[N_SURFACES])
{
	fprintf(stderr, "entering rtree loop read %d\n", iread);

	s->read_length[iread] = READ_LEN; // HACK!

	int icycle;
	for(icycle=0; icycle < s->read_length[iread]; ++icycle) {
		obj_to_rtree(s->output, 0, isurface, iread, icycle, root);
		obj_to_rtree(s->output, 1, isurface, iread, icycle, root);
	}
}
static void make_rtree_surface(Settings* s, int isurface, struct Node* root[N_SURFACES])
{
	if (s->read == -1) {
		int iread;
		fprintf(stderr, "entering rtree loop surface %d\n", isurface);
		for(iread=0; iread < (N_READS-1); ++iread) {
			make_rtree_read(s, isurface, iread, root);
		}
	} else {
		make_rtree_read(s, isurface, s->read, root);
	}
}

static void make_rtree(Settings* s, struct Node* root[N_SURFACES])
{	// Init Rtrees
	int isurface;
	for (isurface = 0 ; isurface < N_SURFACES; ++isurface) {
		root[isurface] = RTreeNewIndex();
	}
	// Create rtrees from objects
	if (s->surface == -1) {
		for(isurface=0; isurface < N_SURFACES; ++isurface) {
			make_rtree_surface(s, isurface, root);
		}
	} else {
		make_rtree_surface(s, s->surface, root);
	}
}

/*
 * Read in raw mismatch indel and SNP images
 * Transform them to yield object locators
 * pivot object locs to key surface-read tests with value cycle and type (SNP/INDEL) for easy processing
 */
static void make_filter(Settings *s)
{
	fprintf(stderr, "entering filter loop\n");

	if (s->surface == -1) {
		int isurface;
		for(isurface=0; isurface < N_SURFACES; ++isurface) {
			make_filter_surface(s, isurface);
		}
	} else {
		make_filter_surface(s, s->surface);
	}
}

typedef struct state {
	bam1_t* read;
	bool filter;
	int hit;
	int points[2];
} state_t;

bool ellipse_hit(const struct Rect circle, int points[2])
{
	double a = (circle.boundary[2] - circle.boundary[0])/2.0;
	double b = (circle.boundary[3] - circle.boundary[1])/2.0;
	double x = (double)points[0] - (circle.boundary[0] + a);
	double y = (double)points[1] - (circle.boundary[1] + b);
	
	double in = ((x*x)/(a*a)) + ((y*y)/(b*b));
	
	return in <= 1.0;
}

int filter_read_callback(const struct Rect r, int64_t id, void* arg)
{
	rtree_entry_t* entry = (rtree_entry_t*) id;
	state_t* s = (state_t*) arg;
	if (ellipse_hit(r, s->points)) {
		s->hit++;
		if (entry->idmm == 0) {
			// Kill all INDELs in this version
			s->filter = true;
			return 0; // No further filters need be considered
		} else {
			// Mismatch? flatten just that cycle
			int cycle = entry->cycle;
			if ( s->read->core.l_qseq > cycle && (((s->read->core.flag&BAM_FREVERSE) == BAM_FREVERSE) == (entry->read == 1) ) ) {
				bam1_seq_seti(bam1_seq(s->read), cycle, 15 /*'N'*/);
				bam1_qual(s->read)[cycle] =  0;
			}
		}
	}
	return 1;
}

static int filter_bam_inner(samfile_t * fp_in_bam, samfile_t * fp_out_bam,
			   size_t * nreads, size_t * nfiltered, struct Node* rtrees[N_SURFACES])
{
	bam1_t* bam = bam_init1();
	while (1) {
		++(*nreads);
		//process read to get x y
		int bam_lane = -1, bam_tile = -1, bam_read = -1, bam_x = -1, bam_y = -1;
		
		if (parse_bam_readinfo(fp_in_bam, bam, &bam_lane, &bam_tile, &bam_x, &bam_y, &bam_read, NULL)) {
			break;	/* break on end of BAM file */
		}
		
		// Parse tile info to reveal detail
		char parseTile[10];
		snprintf(parseTile, 10, "%d", bam_tile);
		int surface = parseTile[0] - '1';
		int swath = parseTile[1] - '1';
		int tile = atoi(parseTile+2)-1;
		bam_x += (swath*20480); // FIXME: get these two constants from settings?
		bam_y += (tile*100000);
		// transform X and Y to match transform used to create images
		bam_x /= 10 * DOWNSAMPLE_AMOUNT;
		bam_y /= 10 * DOWNSAMPLE_AMOUNT;

		
		const struct Node* rtree = rtrees[surface];
		struct Rect search_rect = {
			{bam_x, bam_y, bam_x, bam_y}
		};

		state_t* s = (state_t*)malloc(sizeof(state_t));
		s->read = bam;
		s->hit = 0;
		s->filter = false;
		s->points[0] = bam_x; s->points[1] = bam_y;

		RTreeSearch(rtree, &search_rect, &filter_read_callback, s);

		if (!s->filter) {
			if (0 > samwrite(fp_out_bam, bam)) die("Error: writing bam file\n");
		} else {
			++(*nfiltered);
		}
	}
	bam_destroy1(bam);

	return 0;
}


static int filter_bam(Settings * s)
{
	samfile_t * fp_in_bam = NULL;
	samfile_t * fp_out_bam = NULL;

	fp_in_bam = samopen(s->in_bam_file, "rb", 0);
	if (NULL == fp_in_bam) {
		die("ERROR: can't open bam file %s: %s\n", s->in_bam_file, strerror(errno));
	}

	fp_out_bam = samopen(s->output, "wb", fp_in_bam->header);
	if (NULL == fp_out_bam) {
		die("ERROR: can't open bam file %s: %s\n", s->output, strerror(errno));
	}

	size_t n_reads = 0;
	size_t n_filtered = 0;
	
	struct Node* rtree[N_SURFACES];
	
	make_rtree(s, rtree);
	
	if (0 != filter_bam_inner(fp_in_bam, fp_out_bam, &n_reads, &n_filtered, rtree )) return 1;
	fprintf(stderr, "n_reads: %zu n_filtered: %zu\n", n_reads, n_filtered);
	
	samclose(fp_out_bam);
	samclose(fp_in_bam);
	return 0;
}


typedef struct state_dbg {
	bool idfilter;
	bool mmfilter;
	int hit;
	int points[2];
} state_dbg_t;


int filter_debug_callback(const struct Rect r, int64_t id, void* arg)
{
	rtree_entry_t* entry = (rtree_entry_t*) id;
	state_dbg_t* s = (state_dbg_t*) arg;
	if (ellipse_hit(r, s->points)) {
		s->hit++;
		if (entry->idmm == 0) {
			// Kill all INDELs in this version
			s->idfilter = true;
			return 0; // No further filters need be considered
		} else {
			// Mismatch? flatten just that cycle
			s->mmfilter = true;
		}
	}
	return 1;
}

#define ROWBINARYSET_NODS(x,y,value_array) value_array[y][x/(8)]|=128>>(x)%8

static int dump_object_map(Settings * s)
{
	struct Node* rtrees[N_SURFACES];
	
	make_rtree(s, rtrees);
		
	int surf;
	for (surf = 0; surf < N_SURFACES; ++surf) {
		int y;
		TileImage_t result_any;
		TileImage_t result_id;
		TileImage_t result_mm;
		create_image(&result_any, s->output, "res", surf, 0, 0);
		create_image(&result_id, s->output, "res_id", surf, 0, 0);
		create_image(&result_mm, s->output, "res_mm", surf, 0, 0);

		for (y = 0; y < Y_LEN; ++y) {
			int x;
			for (x = 0; x < X_LEN; ++x) {
				const struct Node* rtree = rtrees[surf];
				struct Rect search_rect = {
					{x, y, x, y}
				};
				
				state_dbg_t* s = (state_dbg_t*)malloc(sizeof(state_dbg_t));
				s->hit = 0;
				s->idfilter = false;
				s->mmfilter = false;
				s->points[0] = x; s->points[1] = y;
				
				if (RTreeSearch(rtree, &search_rect, &filter_debug_callback, s))
				{
					ROWBINARYSET_NODS(x,y,result_any.bitmap);
				}
				if (s->idfilter) {
					ROWBINARYSET_NODS(x,y,result_id.bitmap);
				}
				if (s->mmfilter) {
					ROWBINARYSET_NODS(x,y,result_mm.bitmap);
				}
			}
		}
		write_close_image(&result_any);
		write_close_image(&result_id);
		write_close_image(&result_mm);
	}
	
	return 0;
}



static void usage(int code)
{
	FILE *usagefp = stderr;

	fprintf(usagefp, "spatial_filter_mkII %s\n\n", version);
	fprintf(usagefp,
		"Usage: spatial_filter_mkII [command] [options] bam_file\n"
		"" "  calculate or apply a spatial filter\n" "");
	fprintf(usagefp, "  command must be one of:\n");
	fprintf(usagefp, "    -d         just dump bam file in 'mismatch' format\n");
	fprintf(usagefp, "    -D         just dump filter file in ascii text format to stdout\n");
	fprintf(usagefp, "    -c         calculate filter files\n");
	fprintf(usagefp, "    -a         apply filter files\n");
	fprintf(usagefp, "    -v         display version and exit\n");
	fprintf(usagefp, "\n");
	fprintf(usagefp, "  options:\n");
	fprintf(usagefp, "    -q         Quiet\n");
	fprintf(usagefp, "               Inhibit all progress messages\n");
	fprintf(usagefp, "\n");
	fprintf(usagefp, "  comand specific options:\n");
	fprintf(usagefp, "\n");
	fprintf(usagefp, "    dump bam file:\n");
	fprintf(usagefp, "      none:\n");
	fprintf(usagefp, "\n");
	fprintf(usagefp, "    all other commands require:\n");
	fprintf(usagefp, "      -F --filter file\n");
	fprintf(usagefp, "                  Filter filename e.g. 8088.filter\n");
	fprintf(usagefp, "                  no default: must be supplied\n");
	fprintf(usagefp, "\n");
	fprintf(usagefp, "    calculate filter:\n");
	fprintf(usagefp, "      -s --snp_file file\n");
	fprintf(usagefp, "                 set of snps to be removed\n");
	fprintf(usagefp, "                 file in Reference Ordered Data (ROD) format\n");
	fprintf(usagefp, "\n");
	fprintf(usagefp, "    apply filter:\n");
	fprintf(usagefp, "      -o         output\n");
	fprintf(usagefp, "                 Output bam file name\n");
	fprintf(usagefp, "                 default: stdout\n");
	fprintf(usagefp, "      -u         do not compress the output bam file\n");
	fprintf(usagefp, "                 default: compress\n");
	fprintf(usagefp, "      -f         mark filtered reads as QCFAIL\n");
	fprintf(usagefp, "                 default: do not output filtered read\n");
	fprintf(usagefp, "\n");

	exit(code);
}


/*
 * Make the filter
 */
static void calculate_filter(Settings *s)
{
	samfile_t *fp_input_bam;
	int ntiles = 0;
	size_t nreads = 0;

	// One per surface
	TileImage_t* tile_img_mismatch[N_SURFACES][(N_READS-1)];
	TileImage_t* tile_img_indel[N_SURFACES][(N_READS-1)];

	fp_input_bam = samopen(s->in_bam_file, "rb", 0);
	if (NULL == fp_input_bam) {
		die("ERROR: can't open bam file %s: %s\n", s->in_bam_file, strerror(errno));
	}

	make_tile_images(s, fp_input_bam, tile_img_mismatch, tile_img_indel, &ntiles, &nreads);

	/* close the bam file */
	samclose(fp_input_bam);

	/* back to where we belong */
	checked_chdir(s->working_dir);
}


int main(int argc, char **argv)
{
	Settings settings;
	char *cmd = NULL;

	settings.quiet = false;
	settings.calculate_i = false;
	settings.calculate_ii = false;
	settings.apply = false;
	settings.qcfail = false;
	settings.snp_file = NULL;
	settings.snp_hash = NULL;
	settings.output = NULL;
	settings.in_bam_file = NULL;
	settings.read_length[0] = 0;
	settings.read_length[1] = 0;
	settings.read_length[2] = 0;
	settings.working_dir = NULL;
	settings.read = -1;
	settings.surface = -1;
	settings.min_cycle_idx = -1;
	settings.max_cycle_idx = -1;
	settings.compress = 1;
	settings.dump_label_image = false;
	bool dump_obj_map = false;

	static struct option long_options[] = {
		{"snp_file", required_argument, 0, 's'},
		{"help", 0, 0, 'h'},
		{"filter", 1, 0, 'F'},
		{"version", 0, 0, 'v'},
		{"surface", required_argument, 0, 'e'},
		{"read", required_argument, 0, 'r'},
		{"min_cycle", required_argument, 0, 'm'},
		{"max_cycle", required_argument, 0, 'M'},
		{0, 0, 0, 0}
	};

	int ncmd = 0;
	char c;
	while ( (c = getopt_long(argc, argv, "vdcCafuDF:o:i:p:s:x:y:e:r:m:M:qh?", long_options, 0)) != -1) {
		switch (c) {
			case 'v':	display("spatial_filter: Version %s\n", version);
						exit(0);
			case 'c':	settings.calculate_i = true; ncmd++; break;
			case 'C':	settings.calculate_ii = true; ncmd++; break;
			case 'a':	settings.apply = true; ncmd++; break;
			case 'f':	settings.qcfail = 1;		break;
			case 'u':	settings.compress = 0;		break;
			case 'o':	settings.output = optarg;	break;
			case 's':	settings.snp_file = optarg;	break;
			case 'q':	settings.quiet = 1;			break;
			case 'e':	settings.surface = atoi(optarg); break;
			case 'r':	settings.read = atoi(optarg); break;
			case 'm':	settings.min_cycle_idx = atoi(optarg) - 1; break;
			case 'M':	settings.max_cycle_idx = atoi(optarg); break;
			case 'd':	settings.dump_label_image = true; break;
			case 'D':	dump_obj_map = true; break;
			case 'h':
			case '?':	usage(0);					break;
			default:	display("ERROR: Unknown option %c\n", c);
						usage(1);
						break;
		}
	}

	if (ncmd > 1) {
		display("ERROR: More than one command specified\n", c);
		usage(1);
	}

	if (optind < argc) settings.in_bam_file = argv[optind];

	if (!settings.in_bam_file && (settings.calculate_i || settings.apply) ) die("Error: no BAM file specified\n");

	// create pseudo command line
	if (settings.calculate_i) {
		cmd = smalloc(2048);
		strcat(cmd, argv[0]);
		strcat(cmd, " -c ");
		if (settings.snp_file)                   { strcat(cmd, " -s "); strcat(cmd, settings.snp_file); }
		strcat(cmd, " ");
		strcat(cmd, settings.in_bam_file);
		if (strlen(cmd) > 2047) die("Command line too big");
	}
	if (settings.apply) {
		cmd = smalloc(2048);
		strcat(cmd, argv[0]);
		strcat(cmd, " -a ");
		if (settings.qcfail)    { strcat(cmd, " -f "); }
		if (!settings.compress) { strcat(cmd, " -u "); }
		if (settings.output)    { strcat(cmd, " -o "); strcat(cmd, settings.output); }
		strcat(cmd, " ");
		if (settings.in_bam_file) strcat(cmd, settings.in_bam_file);
		if (strlen(cmd) > 2047) die("Command line too big");
	}

	if (!settings.quiet) display("Cmd: %s\n", cmd);
	settings.cmdline = cmd;

	/* preserve starting directory */
	settings.working_dir = getcwd(NULL,0);
	if (NULL == settings.working_dir) {
		die("ERROR: can't obtain working directory: %s\n", strerror(errno));
	}
	

	/* calculate the filter */
	if (settings.calculate_i) {
		/* read the snp_file */
		if (NULL != settings.snp_file) {
			settings.snp_hash = readSnpFile(settings.snp_file);
			if (NULL == settings.snp_hash) {
				die("ERROR: reading snp file %s\n", settings.snp_file);
			}
		}

		calculate_filter(&settings);
	}
	if (settings.calculate_ii) {
		make_filter(&settings);
	}
	

	if (settings.apply) {
		filter_bam(&settings);
	}
	
	if (dump_obj_map) {
		dump_object_map(&settings);
	}

	if (NULL != settings.working_dir) free(settings.working_dir);

	return EXIT_SUCCESS;

}
