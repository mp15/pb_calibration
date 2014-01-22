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

typedef struct {
	char *cmdline;
	char *filter;
	char *snp_file;
	char *in_bam_file;
	HashTable *snp_hash;
	HashTable *tile_hash;
    int *tileArray;
	char *working_dir;
	char *output;
	int read_length[N_READS];
	int dump;
	int calculate;
	int apply;
	int qcfail;
	int quiet;
	int region_size;
	int nregions_x;
	int nregions_y;
	int nregions;
	int compress;
	int region_min_count;
	float region_mismatch_threshold;
	float region_insertion_threshold;
	float region_deletion_threshold;
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

#define ROWBINARYSET(x,y,value_array) value_array[y/DOWNSAMPLE_AMOUNT][x/(8*DOWNSAMPLE_AMOUNT)]|=1<<(x/DOWNSAMPLE_AMOUNT)%8

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

	png_init_io(img->png, img->file_ptr);
	png_set_IHDR(img->png, img->png_header, X_LEN, Y_LEN, 1, PNG_COLOR_TYPE_GRAY, PNG_INTERLACE_NONE, PNG_COMPRESSION_TYPE_DEFAULT, PNG_FILTER_TYPE_DEFAULT);
	png_write_info(img->png, img->png_header);
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
	
	png_init_io(img->png, img->file_ptr);
	png_set_IHDR(img->png, img->png_header, X_LEN, Y_LEN, 8, PNG_COLOR_TYPE_GRAY, PNG_INTERLACE_NONE, PNG_COMPRESSION_TYPE_DEFAULT, PNG_FILTER_TYPE_DEFAULT);
	png_write_info(img->png, img->png_header);
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

static void writeCloseImage(TileImage_t* img)
{
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

static bool updateSurfaceCycleImage(Settings *s, TileImage_t** row_mismatch_image, TileImage_t** row_indel_image, int read, int x, int y, int *read_mismatch) {
	int cycle;
	y /= 10;
	x /= 10;
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
 * Takes the bam file as input and updates the region table
 *
 * Assumption: within a single input file, all reads are the same length and
 * we're using unclipped data.
 *
 * Returns: 0 written for success
 *	   -1 for failure
 */
static const int N_SURFACES = 2;

void makeTileImages(Settings *s, samfile_t *fp_bam, TileImage_t* tile_img_mismatch[N_SURFACES][(N_READS-1)], TileImage_t* tile_img_indel[N_SURFACES][(N_READS-1)], int *ntiles, size_t * nreads)
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
			s->read_length[iread] = 100; // HACK!
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

		if (!updateSurfaceCycleImage(s, tile_img_mismatch[surface], tile_img_indel[surface], (bam_read-1), bam_x, bam_y, bam_read_mismatch)) {
			die("ERROR: updating image values for surface %i.\n", surface);
		}
		nreads_bam++;
	}

	bam_destroy1(bam);
	
    for(isurface=0;isurface<N_SURFACES; ++isurface) {
		for(iread=0; iread<(N_READS-1); ++iread) {
			for(icycle=0; icycle < s->read_length[iread]; ++icycle) {
				writeCloseImage(&tile_img_mismatch[isurface][iread][icycle]);
				writeCloseImage(&tile_img_indel[isurface][iread][icycle]);
			}
		}
	}

	*nreads = nreads_bam;
}

#define PRECISION 0.6
double** makeGaussian(double sigma, size_t * n_out)
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

void applyGaussianAndThreshold(png_bytepp row_p, png_bytepp output_rows, const int width, const int height, double** kernel, const size_t n)
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

typedef struct roi {
	int x;
	int y;
	int width;
	int height;
} roi_t;

TileImage_t* readImage(const char* fn)
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

void init_uf_array(uf_array_t* array)
{
	array->max_uf = 100;
	array->next_label = 1;
	array->parent = calloc(array->max_uf,sizeof(int));
}

static const int UF_INCREMENT = 100;

void uf_union(int parent, int child, uf_array_t* uf_array_data)
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

/*
 * @returns int[height][width] array of labels corresponding to bitmap
 */
unsigned char** connected_four(png_bytepp bitmap, const int width, const int height)
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
	printf("max label before reduction: %zu\n", uf_array_data.next_label);
	size_t ml_ii = 0;
	// second pass: replace temp labels by equiv class
	for (y_iter = 0; y_iter < height; ++y_iter) {
		for (x_iter = 0; x_iter < width; ++x_iter) {
			if (bitmap[y_iter][x_iter] == BACKGROUND_COLOUR) continue;  // ignore white pixels
			
			label_map[y_iter][x_iter] = uf_find(label_map[y_iter][x_iter], &uf_array_data);
			ml_ii = label_map[y_iter][x_iter] > ml_ii ? label_map[y_iter][x_iter] : ml_ii;
		}
	}
	printf("max label after reduction: %zu\n", ml_ii);
	int loop_iter;
	int count = 0;
	int* transform_parent = malloc(sizeof(int)*ml_ii);
	for ( loop_iter = 0; loop_iter < ml_ii; ++loop_iter ) { if (uf_array_data.parent[loop_iter] == 0) {  transform_parent[loop_iter] = count++; } }

	printf("max label after 2x reduction will be: %u\n", count);
	
	xywh_t* objects = (xywh_t*)malloc(sizeof(xywh_t) * count);
	int object_iter;
	// init the structs
	for (object_iter = 0; object_iter < count; ++object_iter) {
		xywh_t* this_obj = objects + object_iter;
		this_obj->x = width-1;
		this_obj->y = height-1;
		this_obj->xw = 0;
		this_obj->yh = 0;
	}
	// third pass: reduce labels this should probably be folded into 2nd pass
	for (y_iter = 0; y_iter < height; ++y_iter) {
		for (x_iter = 0; x_iter < width; ++x_iter) {
			int label = transform_parent[label_map[y_iter][x_iter]];
			xywh_t* this_obj = objects + label;
			if ( this_obj->x > x_iter ) this_obj->x = x_iter;
			if ( this_obj->y > y_iter ) this_obj->y = y_iter;
			if ( this_obj->xw < x_iter ) this_obj->xw = x_iter;
			if ( this_obj->yh < y_iter ) this_obj->yh = y_iter;
		}
	}
	
	int print_obj_iter;
	printf("dumping object list:\n");
	for (print_obj_iter = 0; print_obj_iter < count; ++print_obj_iter)
	{
		xywh_t* this_obj = objects + print_obj_iter;
		printf("%d: (%d,%d)-(%d,%d)\n",print_obj_iter, this_obj->x, this_obj->y, this_obj->xw, this_obj->yh );
	}

	return label_map;
}



void dumpMap(unsigned char** map)
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
	
	img->file_ptr = fopen("map.png", "wb");
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

void make_filter_image(Settings *s, TileImage_t* image)
{
	// Read image file
	// Convert to grayscale
	
	// Gaussian convolution 10 pixel radius sigma
	// Threshold back to binary
	TileImage_t* outimg = create_gray_image(NULL, "hack", "filter", 1, 1, 99);
	size_t n;
	double** kernel = makeGaussian(10, &n);
	applyGaussianAndThreshold(image->bitmap, outimg->bitmap, png_get_image_width(image->png, image->png_header), png_get_image_height(image->png, image->png_header), kernel, n);
	// Detect ROI by 4 connected labelling
	unsigned char** map = connected_four(outimg->bitmap, png_get_image_width(image->png, image->png_header), png_get_image_height(image->png, image->png_header));
	dumpMap(map);
	
	// Add to hash
	/// HACK
	writeCloseImage(outimg);
}

void make_filter(Settings *s)
{
	TileImage_t* image = readImage("arun2_mm_1_1_99.png");
	make_filter_image(s, image);
	
}

int filter_bam_new(Settings * s, samfile_t * fp_in_bam, samfile_t * fp_out_bam,
			   size_t * nreads, size_t * nfiltered, xywh_t* objects, size_t count)
{
#if 0
	while (1) {
		++(nreads);
		//process read to get x y
		int bam_lane = -1, bam_tile = -1, bam_read = -1, bam_x = -1, bam_y = -1;
		
		if (parse_bam_readinfo(fp_bam, bam, &bam_lane, &bam_tile, &bam_x, &bam_y, &bam_read, NULL)) {
			break;	/* break on end of BAM file */
		}
		int i;
		bool filtered = false;
		for (i = 1); i < count; ++i) {
			xywh_t* this_obj = objects + i;
			if ( this_obj->x <= bam_x && this_obj->xw > bam_x && this_obj->y <= bam_y && this_obj->yh > bam_y ) filtered = true;
		}
		if (!filtered) {
			samwrite(fp_out_bam, header);
			++(*nfiltered);
		}
	}
#endif
	return 0; // GNDN
}



static void usage(int code)
{
	FILE *usagefp = stderr;

	fprintf(usagefp, "spatial_filter %s\n\n", version);
	fprintf(usagefp,
		"Usage: spatial_filter [command] [options] bam_file\n"
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
	fprintf(usagefp, "      --region_size\n");
	fprintf(usagefp, "                 default %d\n", REGION_SIZE);
	fprintf(usagefp, "      --region_min_count\n");
	fprintf(usagefp, "                 minimum coverage when setting region state\n");
	fprintf(usagefp, "                 default %d\n", REGION_MIN_COUNT);
	fprintf(usagefp, "      --region_mismatch_threshold\n");
	fprintf(usagefp, "                 threshold for setting region mismatch state\n");
	fprintf(usagefp, "                 default %-6.4f\n", REGION_MISMATCH_THRESHOLD);
	fprintf(usagefp, "      --region_insertion_threshold\n");
	fprintf(usagefp, "                 threshold for setting region insertion state\n");
	fprintf(usagefp, "                 default %-6.4f\n", REGION_INSERTION_THRESHOLD);
	fprintf(usagefp, "      --region_deletion_threshold\n");
	fprintf(usagefp, "                 threshold for setting region deletion state\n");
	fprintf(usagefp, "                 default %-6.4f\n", REGION_DELETION_THRESHOLD);
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


void calculateFilter(Settings *s)
{
	samfile_t *fp_input_bam;
	int ntiles = 0;
	size_t nreads = 0;

	// One per surface
	TileImage_t* tile_img_mismatch[N_SURFACES][(N_READS-1)];
	TileImage_t* tile_img_indel[N_SURFACES][(N_READS-1)];

    if( NULL == s->filter) {
        display("Writing filter to stdout\n");
        s->filter = "/dev/stdout";
    }

	fp_input_bam = samopen(s->in_bam_file, "rb", 0);
	if (NULL == fp_input_bam) {
		die("ERROR: can't open bam file %s: %s\n", s->in_bam_file, strerror(errno));
	}

	makeTileImages(s, fp_input_bam, tile_img_mismatch, tile_img_indel, &ntiles, &nreads);

	/* close the bam file */
	samclose(fp_input_bam);

	if (!s->quiet) {
		display("Processed %8lu traces\n", nreads);
		if (NULL != s->snp_hash) {
			size_t nsnps = 0;
			int ibucket;
			for (ibucket = 0; ibucket < s->snp_hash->nbuckets; ibucket++) {
				HashItem *hi;
				for (hi = s->snp_hash->bucket[ibucket]; hi; hi = hi->next)
					if (hi->data.i) nsnps += hi->data.i;
			}
			display("Ignored %lu snps\n", nsnps);
		}
	}

	/* back to where we belong */
	checked_chdir(s->working_dir);

	//findBadRegions(s, ntiles, rts_hash);

    if( NULL == s->filter) {
        display("Writing filter to stdout\n");
        s->filter = "/dev/stdout";
    }

	//printFilter(s, ntiles, rts_hash);

	//freeRTS(s, rts_hash);
}


int main(int argc, char **argv)
{
	Settings settings;
	int dumpFilter = 0;
	char *cmd = NULL;

	settings.filter = NULL;
	settings.quiet = 0;
	settings.dump = 0;
	settings.calculate = 0;
	settings.apply = 0;
	settings.qcfail = 0;
	settings.snp_file = NULL;
	settings.snp_hash = NULL;
	settings.tile_hash = NULL;
	settings.tileArray = NULL;
	settings.output = NULL;
	settings.in_bam_file = NULL;
	settings.read_length[0] = 0;
	settings.read_length[1] = 0;
	settings.read_length[2] = 0;
	settings.working_dir = NULL;
	settings.region_size = REGION_SIZE;
	settings.nregions_x = 0;
	settings.nregions_y = 0;
	settings.nregions = 0;
	settings.compress = 1;
	settings.region_min_count = REGION_MIN_COUNT;
	settings.region_mismatch_threshold = REGION_MISMATCH_THRESHOLD;
	settings.region_insertion_threshold = REGION_INSERTION_THRESHOLD;
	settings.region_deletion_threshold = REGION_DELETION_THRESHOLD;

	static struct option long_options[] = {
                   {"snp_file", 1, 0, 's'},
                   {"snp-file", 1, 0, 's'},
                   {"help", 0, 0, 'h'},
                   {"filter", 1, 0, 'F'},
                   {"version", 0, 0, 'v'},
                   {"region_min_count", 1, 0, 'm'},
                   {"region-size", 1, 0, 'r'},
                   {"region_size", 1, 0, 'r'},
                   {"region_mismatch_threshold", 1, 0, 'z'},
                   {"region_insertion_threshold", 1, 0, 'b'},
                   {"region_deletion_threshold", 1, 0, 'e'},
                   {0, 0, 0, 0}
               };

	int ncmd = 0;
	char c;
	while ( (c = getopt_long(argc, argv, "vdcafuDF:b:e:o:i:m:p:s:r:x:y:t:z:qh?", long_options, 0)) != -1) {
		switch (c) {
			case 'v':	display("spatial_filter: Version %s\n", version); 
						exit(0);
                        case 'd':	settings.dump = 1; ncmd++; break;
			case 'D':	dumpFilter = 1; ncmd++; break;
			case 'c':	settings.calculate = 1; ncmd++; break;
			case 'a':	settings.apply = 1; ncmd++; break;
			case 'f':	settings.qcfail = 1;		break;
			case 'u':	settings.compress = 0;		break;
			case 'o':	settings.output = optarg;	break;
			case 's':	settings.snp_file = optarg;	break;
			case 'F':	settings.filter = optarg;	break;
			case 'r':	settings.region_size = atoi(optarg); break;
			case 'm':	settings.region_min_count = atoi(optarg); break;
			case 'z':	settings.region_mismatch_threshold = atof(optarg); break;
			case 'b':	settings.region_insertion_threshold = atof(optarg); break;
			case 'e':	settings.region_deletion_threshold = atof(optarg); break;
			case 'q':	settings.quiet = 1;			break;
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

	if (!settings.in_bam_file && !dumpFilter) die("Error: no BAM file specified\n");

        if (!settings.filter && (dumpFilter || settings.apply)) die("Error: no filter file specified\n");

	if (settings.calculate) {
   	    if (settings.region_size < 1) die("Error: invalid region size");

	    if (settings.region_min_count < 1) die("Error: invalid region_min_count");

#if 0 // this code will reset region_min_count so that at least 2 reads are required to pass any threshold
            int region_min_count = settings.region_min_count;

	    if ((region_min_count * settings.region_mismatch_threshold) < 1.0 ) {
                region_min_count = ceil(1.0 / settings.region_mismatch_threshold);
                display("Resetting region_min_count to %d\n", region_min_count);
            }
	    if ((region_min_count * settings.region_insertion_threshold) < 1.0 ) {
                region_min_count = ceil(1.0 / settings.region_insertion_threshold);
                display("Resetting region_min_count to %d\n", region_min_count);
            }
	    if ((region_min_count * settings.region_deletion_threshold) < 1.0 ) {
                region_min_count = ceil(1.0 / settings.region_deletion_threshold);
                display("Resetting region_min_count to %d\n", region_min_count);
            }
            settings.region_min_count = region_min_count;
#endif            
        }

	// create pseudo command line
	if (settings.calculate) {
		char arg[64];
		cmd = smalloc(2048);
		strcat(cmd, argv[0]);
		strcat(cmd, " -c ");
		if (settings.snp_file)                   { strcat(cmd, " -s "); strcat(cmd, settings.snp_file); }
		if (settings.filter)                     { strcat(cmd, " -F "); strcat(cmd, settings.filter); }
		if (settings.region_size)                { snprintf(arg, 64, " --region_size %d", settings.region_size);
                                                           strcat(cmd, arg); }
		if (settings.region_min_count)           { snprintf(arg, 64, " --region_min_count %d", settings.region_min_count);
                                                           strcat(cmd, arg); }
		if (settings.region_mismatch_threshold)  { snprintf(arg, 64, " --region_mismatch_threshold %-6.4f", settings.region_mismatch_threshold);
                                                           strcat(cmd, arg); }
		if (settings.region_insertion_threshold) { snprintf(arg, 64, " --region_insertion_threshold %-6.4f", settings.region_insertion_threshold);
                                                           strcat(cmd, arg); }
		if (settings.region_deletion_threshold)  { snprintf(arg, 64, " --region_deletion_threshold %-6.4f", settings.region_deletion_threshold);
                                                           strcat(cmd, arg); }
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
		if (settings.filter)    { strcat(cmd, " -F "); strcat(cmd, settings.filter); }
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
	
	/// HACK TEST
	make_filter(&settings);
	///
	

	/* calculate the filter */
    if (settings.calculate) {
        /* read the snp_file */
        if (NULL != settings.snp_file) {
            settings.snp_hash = readSnpFile(settings.snp_file);
            if (NULL == settings.snp_hash) {
                die("ERROR: reading snp file %s\n", settings.snp_file);
            }
        }

        calculateFilter(&settings);
    }

	if (NULL != settings.working_dir) free(settings.working_dir);

	return EXIT_SUCCESS;

}
