//*  -*- mode: c; indent-tabs-mode: nil; c-basic-offset: 4; tab-width: 8; -*- */

/* TO-DO:
 *
 */

/*
 * Copyright (c) 2006-2009,2013, Genome Research Ltd (GRL).
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
 * Author: Martin Pollard, 2013 *
 * This code looks for spatial features given an aligned bam file
 *
 */

/*
 * various compile time options, either uncomment option
 * or compile with CFLAGS = '-D$OPTION ..'
 *
 * QC_FAIL
 *   ignore reads that fail QC when building calibration table
 *
 * PROPERLY_PAIRED
 *   only use properly paired reads when building calibration table
 */

#define QC_FAIL
#define PROPERLY_PAIRED

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

#include <version.h>

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

void freeRTS(Settings *s, HashTable ***rts_hash)
{
        int itile, read, cycle;
        for(itile=0;itile<N_TILES;itile++)
            for(read=0;read<N_READS;read++)
            {
                if( NULL == rts_hash[itile*N_READS+read]) continue;
                for(cycle=0;cycle<s->read_length[read];cycle++)
                {
                    HashTable *rt_hash = rts_hash[itile*N_READS+read][cycle];
                    HashTableDestroy(rt_hash, 1);
                }
                free(rts_hash[itile*N_READS+read]);
            }
}

/*
 * identify bad tiles quality < mean quality - filter * stdev quality
 * filter is typically 2.
*/

static void findBadRegions(Settings *s, int ntiles, HashTable ***rts_hash)
{
	int i;
    HashItem *tileItem, *hashItem;

	if (0 >= ntiles)
		return;

    for (i=0; i<ntiles; i++) {
        int tile = s->tileArray[i];
        tileItem = HashTableSearch(s->tile_hash, (char *)&tile, sizeof(tile));
        if (NULL == tileItem) {
            fprintf(stderr,"ERROR: unknown tile %d\n", s->tileArray[i]);
            exit(EXIT_FAILURE);
        }
		int itile = tileItem->data.i;

		int read;
		for (read = 0; read < N_READS; read++) {
			int cycle;
			for (cycle = 0; cycle < s->read_length[read]; cycle++) {
				// set the state for each region
   	            HashTable *rt_hash = rts_hash[itile*N_READS+read][cycle];
  	            HashIter *iter = HashTableIterCreate();
  	            while ((hashItem = HashTableIterNext(rt_hash, iter))) {
                    RegionTable *rt = (RegionTable *)hashItem->data.p;
                    rt->state = 0;

                    // coverage
                    int n = rt->align + rt->insertion + rt->deletion + rt->soft_clip + rt->known_snp;

                    // coverage - mark spare bins
                    if (n < s->region_min_count) rt->state |= REGION_STATE_COVERAGE;

                    // correct for sparse bins by assuming ALL bins have atleast REGION_MIN_COUNT clusters
                    n = max(n, s->region_min_count);

                    // mismatch - mark bins with maximum mismatch rate > threshold
                    if (((float)rt->mismatch  / (float)n) >= s->region_mismatch_threshold)  rt->state |= REGION_STATE_MISMATCH;
                    // insertion - mark bins with maximum insertion rate > threshold
                    if (((float)rt->insertion / (float)n) >= s->region_insertion_threshold) rt->state |= REGION_STATE_INSERTION;
                    // deletion - mark bins with maximum deletion rate > threshold
                    if (((float)rt->deletion  / (float)n) >= s->region_deletion_threshold)  rt->state |= REGION_STATE_DELETION;
                }
				// ignoring low coverage, if all regions with a non-zero state have the same state and the
                // fraction of regions with this state exceeds a theshold set the state for the whole tile
				int tile_state = -1, nregions = 0;
                HashTableIterReset(iter);
  	            while ((hashItem = HashTableIterNext(rt_hash, iter))) {
                    RegionTable *rt = (RegionTable *)hashItem->data.p;
                    int state = rt->state & ~REGION_STATE_COVERAGE;
                    if (!state) continue;
                    if (tile_state == -1) tile_state = state;
                    if (state != tile_state) break;
                    nregions++;
                }
				if (NULL == hashItem && (((float)nregions/(float)s->nregions) >= TILE_REGION_THRESHOLD)) {
                    HashTableIterReset(iter);
  	                while ((hashItem = HashTableIterNext(rt_hash, iter))) {
                        RegionTable *rt = (RegionTable *)hashItem->data.p;
                        rt->state = tile_state | (rt->state & REGION_STATE_COVERAGE);
                    }
                }
                if (!s->quiet) {
                    int mismatch = 0, insertion = 0, deletion = 0, soft_clip = 0;
                    long quality_bases = 0, quality_errors = 0;
                    HashTableIterReset(iter);
  	                while ((hashItem = HashTableIterNext(rt_hash, iter))) {
                        RegionTable *rt = (RegionTable *)hashItem->data.p;
                        if (rt->state & REGION_STATE_MISMATCH)  mismatch++;
                        if (rt->state & REGION_STATE_INSERTION) insertion++;
                        if (rt->state & REGION_STATE_DELETION)  deletion++;
                        if (rt->state & REGION_STATE_SOFT_CLIP) soft_clip++;
                        quality_bases  += rt->align;
                        quality_errors += rt->mismatch;
                    }
                    float ssc = 1.0;
                    float quality = -10.0 * log10((quality_errors + ssc)/(quality_bases + ssc));
                    display("tile=%-4d read=%1d cycle=%-3d quality=%.2f mismatch=%-4d insertion=%-4d deletion=%-4d soft_clip=%-4d\n",
                            tile, read, cycle, quality, mismatch, insertion, deletion, soft_clip);
                }
			}
		}
	}

	return;
}

void printFilter(Settings *s, int ntiles, HashTable ***rts_hash) 
{
	FILE *fp;
	int i, read, cycle;
	Header hdr;

    fp = fopen(s->filter, "w+");
	if (!fp) die("Can't open filter file %s: %s\n", s->filter, strerror(errno));

	hdr.region_magic = strdup(REGION_MAGIC);
	hdr.coord_shift = COORD_SHIFT; 
	hdr.coord_factor = COORD_FACTOR;
	hdr.ntiles = ntiles;
	hdr.tileArray = s->tileArray;
	hdr.nreads = N_READS;
	hdr.region_size = s->region_size;
	hdr.nregions = s->nregions;
	hdr.nregions_x = s->nregions_x;
	hdr.nregions_y = s->nregions_y;
	for (read=0; read < hdr.nreads; read++)
		hdr.readLength[read] = s->read_length[read];
	hdr.cmdLine = strdup(s->cmdline);
	hdr.ncomments = 0;
	writeHeader(fp,&hdr);
        
    for (i=0; i<ntiles; i++) {
        int tile = s->tileArray[i];
        HashItem *tileItem = HashTableSearch(s->tile_hash, (char *)&tile, sizeof(tile));
        if (NULL == tileItem) {
            fprintf(stderr,"ERROR: unknown tile %d\n", s->tileArray[i]);
            exit(EXIT_FAILURE);
        }
		int itile = tileItem->data.i;
		for (read = 0; read < N_READS; read++) {
			for (cycle = 0; cycle < s->read_length[read]; cycle++) {
                HashTable *rt_hash = rts_hash[itile*N_READS+read][cycle];
                int ix, iy;
                for (ix = 0; ix < s->nregions_x; ix++) {
                    for (iy = 0; iy < s->nregions_y; iy++) {
                        char key[100];
                        char *cp;
                        HashItem *hi;
                        int state = 0;
                        cp = append_int(key, ix);
                        cp = append_char(cp, ':');
                        cp = append_int(cp, iy);
                        *cp = 0;
                        if( NULL != (hi = HashTableSearch(rt_hash, key, strlen(key))) ){
                            RegionTable *rt = (RegionTable *)hi->data.p;
                            state = rt->state;
                        }
   					    fputc(state, fp);
     			    }
				}
			}
		}
	}

	fclose(fp);
}

/*
 * cts - parse bam file line
 *
 * returns 0 on success, 1 on expected failure.
 */
int dump_bam_file(Settings *s, samfile_t *fp_bam, size_t *nreads)
{

	size_t nreads_bam = 0;

	static const int bam_read_buff_size = 1024;
	char bam_read_seq[bam_read_buff_size];
	int bam_read_qual[bam_read_buff_size];
	int bam_read_mismatch[bam_read_buff_size];

	bam1_t *bam = bam_init1();

	/* loop over reads in the bam file */
	while (1) {
		int bam_lane = -1, bam_tile = -1, bam_read = -1, bam_x = -1, bam_y = -1;

		if (parse_bam_readinfo(fp_bam, bam, &bam_lane, &bam_tile, &bam_x, &bam_y, &bam_read, NULL)) {
			/* break on end of BAM file */
			break;
		}

		if (BAM_FUNMAP & bam->core.flag) continue;

		parse_bam_alignments(fp_bam, bam, bam_read_seq, bam_read_qual, NULL, bam_read_mismatch,
                                                  bam_read_buff_size, s->snp_hash);

		char *name = bam1_qname(bam);
		uint8_t *oq_ptr;
		char *oq = NULL;
		int i;

		oq_ptr = bam_aux_get(bam, "OQ");
		if (NULL != oq_ptr) {
			oq = bam_aux2Z(oq_ptr);
			if (NULL == oq) {
				die("ERROR: Invalid original qualities %s for read: \"%s\"\n", oq, name);
			}
		}

		printf("%s\t%d\t%s", name, bam->core.flag, bam_read_seq);
		/* stringify quality values and mismatch bitmap into read_seq */
		for (i = 0; i < bam->core.l_qseq; i++)
			bam_read_seq[i] = bam_read_qual[i] + PHRED_QUAL_OFFSET;
		printf("\t%s", bam_read_seq);
		for (i = 0; i < bam->core.l_qseq; i++)
			bam_read_seq[i] =
			    bam_read_mismatch[i] + PHRED_QUAL_OFFSET;
		printf("\t%s", bam_read_seq);
		if (NULL != oq) {
			if (BAM_FREVERSE & bam->core.flag)
				oq = reverse_seq(oq);
			printf("\t%s", oq);
		}
		printf("\n");

		nreads_bam++;
	}

	bam_destroy1(bam);

	*nreads = nreads_bam;

	return 0;
}


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

static TileImage_t* createImage(TileImage_t* existing, const char* prefix, const char* ftype, int surface, int read, int cycle)
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
static TileImage_t* createGrayImage(TileImage_t* existing, const char* prefix, const char* ftype, int surface, int read, int cycle)
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
				if (createImage(&tile_img_mismatch[isurface][iread][icycle], s->output, "mm", isurface, iread, icycle) == NULL) die("ERROR: allocating image memory surface %i read %i cycle %i.\n", isurface, iread, icycle);
				if (createImage(&tile_img_indel[isurface][iread][icycle], s->output, "id", isurface, iread, icycle) == NULL) die("ERROR: allocating image memory surface %i read %i cycle %i.\n", isurface, iread, icycle);
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

void connected_four(png_bytepp bitmap, const int width, const int height)
{
	// F. Chang, A linear-time component-labeling algorithm using contour tracing technique, Computer Vision and Image Understanding, vol. 93, no. 2, pp. 206-220, 2004.
	// based on: https://en.wikipedia.org/w/index.php?title=Connected-component_labeling&oldid=575300229
	int x_iter, y_iter;
	int next_label = 1;
	const int BACKGROUND = 255;
	int** label_map = malloc(sizeof(int*)*height);
	for (y_iter = 0; y_iter < height; ++y_iter) {
		label_map[y_iter] = calloc(width, sizeof(int));
		for (x_iter= 0; x_iter < width; ++x_iter) {
			if (bitmap[y_iter][x_iter] == BACKGROUND) continue;
			
			if (x_iter != 0 && bitmap[y_iter][x_iter] == bitmap[y_iter][x_iter-1]) {
				label_map[y_iter][x_iter] = label_map[y_iter][x_iter-1];
			} else if ( x_iter != 0 && y_iter != 0
					   && bitmap[y_iter][x_iter] == bitmap[y_iter][x_iter-1]
					   && bitmap[y_iter][x_iter] == bitmap[y_iter-1][x_iter]
					   && (label_map[y_iter][x_iter] != label_map[y_iter][x_iter-1])
					   && (label_map[y_iter][x_iter-1] != label_map[y_iter][x_iter])) {
				label_map[y_iter][x_iter] = label_map[y_iter][x_iter-1] > label_map[y_iter-1][x_iter] ? label_map[y_iter][x_iter-1] : label_map[y_iter-1][x_iter];
			} else if ( x_iter != 0 && y_iter != 0
					   && bitmap[y_iter][x_iter] != bitmap[y_iter][x_iter-1]
					   && bitmap[y_iter][x_iter] == bitmap[y_iter-1][x_iter] ) {
				label_map[y_iter][x_iter] = label_map[y_iter-1][x_iter];
			} else if ( x_iter != 0 && y_iter != 0
					   && bitmap[y_iter][x_iter] != bitmap[y_iter][x_iter-1]
					   && bitmap[y_iter][x_iter] != bitmap[y_iter-1][x_iter] ) {
				label_map[y_iter][x_iter] = next_label++;
			}
		}
	}
	for (y_iter = 0; y_iter < height; ++y_iter) {
		for (x_iter= 0; x_iter < width; ++x_iter) {
			if (bitmap[y_iter][x_iter] == BACKGROUND) continue;
			
			if (x_iter != 0 && bitmap[y_iter][x_iter] == bitmap[y_iter][x_iter-1]) {
				label_map[y_iter][x_iter] = label_map[y_iter][x_iter-1];
			} else if ( x_iter != 0 && y_iter != 0
					   && bitmap[y_iter][x_iter] == bitmap[y_iter][x_iter-1]
					   && bitmap[y_iter][x_iter] == bitmap[y_iter-1][x_iter]
					   && (label_map[y_iter][x_iter] != label_map[y_iter][x_iter-1])
					   && (label_map[y_iter][x_iter-1] != label_map[y_iter][x_iter])) {
				label_map[y_iter][x_iter] = label_map[y_iter][x_iter-1] > label_map[y_iter-1][x_iter] ? label_map[y_iter][x_iter-1] : label_map[y_iter-1][x_iter];
			} else if ( x_iter != 0 && y_iter != 0
					   && bitmap[y_iter][x_iter] != bitmap[y_iter][x_iter-1]
					   && bitmap[y_iter][x_iter] == bitmap[y_iter-1][x_iter] ) {
				label_map[y_iter][x_iter] = label_map[y_iter-1][x_iter];
			} else if ( x_iter != 0 && y_iter != 0
					   && bitmap[y_iter][x_iter] != bitmap[y_iter][x_iter-1]
					   && bitmap[y_iter][x_iter] != bitmap[y_iter-1][x_iter] ) {
				label_map[y_iter][x_iter] = next_label++;
			}
		}
	}
	printf("max label %d", next_label);
}

void make_filter_image(Settings *s, TileImage_t* image)
{
	// Read image file
	// Convert to grayscale
	
	// Gaussian convolution 10 pixel radius sigma
	// Threshold back to binary
	TileImage_t* outimg = createGrayImage(NULL, "hack", "filter", 1, 1, 99);
	size_t n;
	double** kernel = makeGaussian(10, &n);
	applyGaussianAndThreshold(image->bitmap, outimg->bitmap, png_get_image_width(image->png, image->png_header), png_get_image_height(image->png, image->png_header), kernel, n);
	
	// Detect ROI by 4 connected labelling
	connected_four(outimg->bitmap, png_get_image_width(image->png, image->png_header), png_get_image_height(image->png, image->png_header));
	
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
			   size_t * nreads, size_t * nfiltered)
{
	return 0; // GNDN
}

/*
 * Takes a bam file as input and outputs a re-calibrated bam file
 * It uses the associated CIF files too to do this.
 *
 * Assumption: within a single input file, all reads are the same length and
 * we're using unclipped data. We then utilise this to construct a common
 * header to reduce overhead of data.
 *
 * Returns: 0 written for success
 *	   -1 for failure
 */
int filter_bam(Settings * s, samfile_t * fp_in_bam, samfile_t * fp_out_bam,
			   size_t * nreads, size_t * nfiltered)
{
	int lane = -1;
	size_t nreads_bam = 0;
	int nfiltered_bam = 0;


	bam1_t *bam = bam_init1();

	/* loop over reads in the input bam file */
	while (1) {
		int bam_lane = -1, bam_tile = -1, bam_read = -1, read_length, bam_x=-1, bam_y=-1;

		if (parse_bam_readinfo(fp_in_bam, bam, &bam_lane, &bam_tile, &bam_x, &bam_y, &bam_read, NULL)) {
			break;	/* break on end of BAM file */
		}

		read_length = bam->core.l_qseq;

		if (s->read_length[bam_read] != read_length) {
			die("Error: inconsistent read lengths within bam file for read %d.\n"
			    "have length %ld, previously it was %d.\n",
			    bam_read, (long)read_length, s->read_length[bam_read]);
		}

		if (lane == -1) {
			lane = bam_lane;
		}
		if (bam_lane != lane) {
			die("Error: Inconsistent lane: Bam lane %d qseq lane %d.\n", bam_lane, lane);
		}

		nreads_bam++;

		char state = 0, bad_cycle_count = 0;
		int iregion = xy2region(bam_x, bam_y, s->region_size, s->nregions_x, s->nregions_y);
		int read;
		for (read = 0; read < N_READS; read++) {
			int cycle;
			for (cycle = 0; cycle < s->read_length[read]; cycle++) {
				state = getFilterData(bam_tile, read, cycle, iregion);
				if (state & REGION_STATE_MASK)
						bad_cycle_count++;
				}
		}

		if (bad_cycle_count) {
			nfiltered_bam++;
			if (s->qcfail) 
				bam->core.flag |= BAM_FQCFAIL;
			else
				continue;
			}

		if (0 > samwrite(fp_out_bam, bam)) die("Error: writing bam file\n");
	}

	*nreads = nreads_bam;
	*nfiltered = nfiltered_bam;

	bam_destroy1(bam);

	return 0;
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

void applyFilter(Settings *s)
{
	samfile_t *fp_input_bam;
	samfile_t *fp_output_bam;
	char out_mode[5] = "wb";
	char *out_bam_file = NULL;
	bam_header_t *out_bam_header = NULL;
	size_t nreads = 0;
	size_t nfiltered = 0;
	Header hdr;
	FILE *fp;
        int read;

	fp = fopen(s->filter, "rb");
	if (!fp) die("Can't open filter file %s\n", s->filter);
	readHeader(fp, &hdr);
	readFilterData(fp, &hdr);
	fclose(fp);

	s->region_size = hdr.region_size;
	s->nregions_x = hdr.nregions_x;
	s->nregions_y = hdr.nregions_y;

        for (read=0;read<hdr.nreads;read++)
                s->read_length[read] = hdr.readLength[read];

	if (0 == s->compress)
		strcat(out_mode, "u");

	fp_input_bam = samopen(s->in_bam_file, "rb", 0);
	if (NULL == fp_input_bam) {
		die("ERROR: can't open bam file %s: %s\n", s->in_bam_file, strerror(errno));
	}

	out_bam_header = bam_header_dup(fp_input_bam->header);
	char concat_cmd[2048];
	strcpy(concat_cmd, hdr.cmdLine);
	strcat(concat_cmd, " ; ");
	strcat(concat_cmd, s->cmdline);
	bam_header_add_pg("spf", "spatial_filter", "A program to apply a spatial filter", concat_cmd, out_bam_header);

	out_bam_file = (NULL == s->output ? aprintf("/dev/stdout") : ((s->output)[0] == '/' ? aprintf("%s", s->output) : aprintf("%s/%s", s->working_dir, s->output)));
	fp_output_bam = samopen(out_bam_file, out_mode, out_bam_header);
	if (NULL == fp_output_bam) {
		die("ERROR: can't open bam file %s: %s\n", out_bam_file, strerror(errno));
	}
	free(out_bam_file);

	bam_header_destroy(out_bam_header);

	if (-1 == filter_bam(s, fp_input_bam, fp_output_bam, &nreads, &nfiltered)) {
		die("ERROR: failed to filter bam file %s\n", s->in_bam_file);
	}

	samclose(fp_input_bam);
	samclose(fp_output_bam);

	if (!s->quiet) display("Processed %8lu traces\n", nreads);
	if (!s->quiet) display("%s %8lu traces\n", (s->qcfail ? "QC failed" : "Removed"), nfiltered);

	/* back to where we belong */
	checked_chdir(s->working_dir);
}

void dumpBAM(Settings *s)
{
	samfile_t *fp_input_bam;
		size_t nreads = 0;

		fp_input_bam = samopen(s->in_bam_file, "rb", 0);
		if (NULL == fp_input_bam) {
			die("ERROR: can't open bam file %s: %s\n", s->in_bam_file, strerror(errno));
		}

		if (0 != dump_bam_file(s, fp_input_bam, &nreads)) {
			die("ERROR: failed to dump bam file %s\n", s->in_bam_file);
		}

		/* close the bam file */
		samclose(fp_input_bam);

		if (!s->quiet) {
			display("Dumped %8lu traces\n", nreads);
		}
}

void dumpFilterFile(char *filename)
{
	FILE *fp;
	Header hdr;
	int i;

	if (!filename) die("dumpFilterFile: no filter filename given\n");
	fp = fopen(filename, "r");
	if (!fp) die("dumpFilterFile: Can't open file %s\n", filename);
	readHeader(fp,&hdr);
	printf("Magic:          %s\n", hdr.region_magic);
	printf("Coord Shift:    %-5d\n", hdr.coord_shift);
	printf("Coord Factor:   %-5d\n", hdr.coord_shift);
	printf("Region Size:    %-5d\n", hdr.region_size);
	printf("Num Regions:    %-5d\n", hdr.nregions);
	printf("Num Tiles:      %-5d\n", hdr.ntiles);
	for (i=0; i < hdr.ntiles; i++) printf("%-5d ", hdr.tileArray[i]);
	printf("\n");
	printf("Read Length:    ");
	for (i=0; i < hdr.nreads; i++) printf("%-5d ", hdr.readLength[i]);
	printf("\n");
	printf("Command Line:   %s\n", hdr.cmdLine);
	for (i=0; i < hdr.ncomments; i++) {
		if (i) printf("                %s\n", hdr.comments[i]);
		else   printf("Comments:       %s\n", hdr.comments[i]);
	}
	fclose(fp);
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

	/* dump the alignments */
	if (settings.dump) dumpBAM(&settings);

	/* Dump the filter file */
	if (dumpFilter) dumpFilterFile(settings.filter);
	
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

	/* apply the  filter */
	if (settings.apply) applyFilter(&settings);

	if (NULL != settings.working_dir) free(settings.working_dir);

	return EXIT_SUCCESS;

}
