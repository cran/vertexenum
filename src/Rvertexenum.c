/* Original Copyright: David Avis 2003,2011 avis@cs.mcgill.ca         */
/* Modification for R written by Robert Robere, October 2012 */

/* This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
*/

// Includes for the R-C interface
#include <R.h>
#include <Rdefines.h>
#include <Rinternals.h>
#include <Rembedded.h>
// Normal includes
#include <stdio.h>
#include <string.h>
// This is for the vertex enumuration code.
#include "lrslib.h"
#include <R_ext/Rdynload.h>

/* FILE *lrs_cfp;			/\* output file for checkpoint information       *\/ */
/* FILE *lrs_ifp;			/\* input file pointer       *\/ */
/* FILE *lrs_ofp;			/\* output file pointer      *\/ */

unsigned long dict_count, dict_limit, cache_tries, cache_misses;
/* Variables and functions global to this file only */
static long lrs_checkpoint_seconds = 0;
static long lrs_global_count = 0;	/* Track how many lrs_dat records are 
					   allocated */
static lrs_dat_p *lrs_global_list[MAX_LRS_GLOBALS + 1];
static void lrs_dump_state ();

void copy_input(const SEXP A_num, const SEXP A_den, const SEXP b_num, const SEXP b_den, const SEXP dim, lrs_dic *P, lrs_dat *Q) {
  long m = INTEGER(dim)[0];
  long n = INTEGER(dim)[1];
  long num[n+1];
  long den[n+1];
  int i = 0;
  int j = 0;
  for (i = 0; i < m; i++) {
    num[0] = INTEGER(b_num)[i];
    den[0] = INTEGER(b_den)[i];
    for (j = 0; j < n; j++) {
      // Column-major order
      num[j+1] = INTEGER(A_num)[j*m + i];
      den[j+1] = INTEGER(A_den)[j*m + i];
    }
    lrs_set_row(P, Q, (i+1), num, den, 1L);
  }
}

// Produce vertices of system Ax <= b
// Since lrs only works with rational numbers, each input (A, b) is split into
// two: a "numerator" and a "denominator"
// A is dim[0] * dim[1] matrix
// B is dim[0] * 1 vector
// Needed to add nrows and ncols explicitly to make it easier to 
// determine the size of A
SEXP vertexenum(const SEXP A_num, const SEXP A_den, const SEXP b_num, const SEXP b_den, const SEXP dim) {
  lrs_dic *P;			/* structure for holding current dictionary and indices */
  lrs_dat *Q;			/* structure for holding static problem data            */

  lrs_mp_vector output;		/* holds one line of output; ray,vertex,facet,linearity */
  lrs_mp_matrix Lin;		/* holds input linearities if any are found             */
  long col;			/* output column index for dictionary                   */
  long startcol = 0;
  long prune = FALSE;		/* if TRUE, getnextbasis will prune tree and backtrack  */

  // Do some global initialization
  if ( !lrs_init ("t")) {
    return NULL;
  }

  /* global variables lrs_ifp and lrs_ofp are file pointers for input and output   */
  /* they default to stdin and stdout, but may be overidden by command line parms. */
  /* Allocate lrs_dat, lrs_dic and set up the problem */
  Q = lrs_alloc_dat("LRS globals");	/* allocate and init structure for static problem data */

  // Set parameters of Q according to values in SEXP
  Q->m = INTEGER(dim)[0];
  Q->n = INTEGER(dim)[1] + 1;
  if (Q == NULL) {
    error("Error with initial allocation!");
  }
  P = lrs_alloc_dic (Q);	/* allocate and initialize lrs_dic                     */
  if (P == NULL)
    error("Error allocating tableux!");
  // Copy the input sexps to P and Q
  copy_input(A_num, A_den, b_num, b_den, dim, P, Q);
  /* output holds one line of output from dictionary     */
  output = lrs_alloc_mp_vector (Q->n);
  /* Find a starting cobasis from default of specified order               */
  /* P is created to hold  active dictionary data and may be cached        */
  /*         Lin is created if necessary to hold linearity space                   */
  /*         Print linearity space if any, and retrieve output from first dict.    */
  if (!lrs_getfirstbasis (&P, Q, &Lin, TRUE)) {
    // should exit gracefully
    return NULL;
  }
  
  /* Pivot to a starting dictionary                      */
  /* There may have been column redundancy               */
  /* If so the linearity space is obtained and redundant */
  /* columns are removed. User can access linearity space */
  /* from lrs_mp_matrix Lin dimensions nredundcol x d+1  */

  /* for (col = 0L; col < Q->nredundcol; col++)  /\* print linearity space *\/ */
  /*   lrs_printoutput (Q, Lin[col]);      /\* Array Lin[][] holds the coeffs.   *\/ */

  /* We initiate reverse search from this dictionary       */
  /* getting new dictionaries until the search is complete */
  /* User can access each output line from output which is */
  /* vertex/ray/facet from the lrs_mp_vector output         */
  /* prune is TRUE if tree should be pruned at current node */
  int numVertices = 0;
  int oldAllocated = 3;
  int allocated = 3;
  int i = 0;
  int j = 0;
  lrs_mp_matrix matrix = lrs_alloc_mp_matrix(allocated, Q->n);
  int tmpMatrixAllocated = 0;
  lrs_mp_matrix tmpMatrix;
  // stores the denominators of the extreme rays, if any
  /* lrs_mp_vector ray_denom = lrs_alloc_mp_vector(allocated); */
  /* lrs_mp_vector tmp_ray_denom; */
  do {
    for (col = 0; col <= P->d; col++) {
      if (lrs_getsolution (P, Q, matrix[numVertices], col)) {
	//lrs_printoutput(Q, matrix[numVertices]);
	numVertices++;
	/* if (zero(matrix[numVertices][0])) { */
	/*   // extreme ray */
	/*   ray_denom[numVertices] = P->det; */
	/* } else { */
	/*   ray_denom[numVertices] = 1; */
	/* } */
	if (numVertices == allocated) {
	  if (tmpMatrixAllocated) {
	    lrs_clear_mp_matrix(tmpMatrix, oldAllocated, Q->n);
	  } else {
	    // first time allocating tmpMatrix
	    tmpMatrixAllocated = 1;
	  }
	  //printf("\n\n");
	  //printf("Copying...\n");
	  oldAllocated = allocated;
	  allocated *= 2;
	  // First copy the matrix
	  tmpMatrix = matrix;
	  matrix = lrs_alloc_mp_matrix(allocated, Q->n);
	  for (i = 0; i < numVertices; i++) {
	    for (j = 0; j < Q->n; j++) {
	      // maybe need to explictly copy it
	      copy(matrix[i][j], tmpMatrix[i][j]);
	      //prat("", matrix[i][j], matrix[i][0]);
	    }
	    //printf("\n");
	  }
	  lrs_clear_mp_matrix(tmpMatrix, oldAllocated, Q->n);
	  // Now copy ray_denom
	  /* tmp_ray_denom = ray_denom; */
	  /* ray_denom = lrs_alloc_mp_vector(allocated); */
	  /* for (i = 0; i < numVertices; i++) { */
	  /*   copy(ray_denom[i], tmp_ray_denom[i]); */
	  /* } */
	}
      }
    }
  } while (!Q->lponly && lrs_getnextbasis (&P, Q, prune));

  //printf("\n\n");
  // Now we record the points we've seen into an R matrix.
  SEXP points;
  double tmpDoub = 0;
  PROTECT(points = allocMatrix(REALSXP, numVertices, Q->n));
  for (i = 0; i < numVertices; i++) {
    for (j = 0; j < Q->n; j++) {
      if (zero(matrix[i][0])) {
	// Extreme ray
	mptodouble(matrix[i][j], &tmpDoub);
	//rattodouble(matrix[i][j], ray_denom[i], &tmpDoub);
      } else {
	// Vertex: matrix[i][0] stores denom
	rattodouble(matrix[i][j], matrix[i][0], &tmpDoub);
	//pmp("", matrix[i][0]);
      }
      REAL(points)[i + numVertices*j] = tmpDoub;
      //printf("%f ", tmpDoub);
    }
    //printf("\n");
  }
  UNPROTECT(1);

  //printf("\n\n");
  for (i = 0; i < numVertices; i++) {
    for (j = 0; j < Q->n; j++) {
      //prat("", matrix[i][j], matrix[i][0]);
    }
    //printf("\n");
  }

  // free up matrix
  lrs_clear_mp_matrix(matrix, allocated, Q->n);
  lrs_clear_mp_vector(output, Q->n);
  lrs_free_dic (P,Q);           /* deallocate lrs_dic */
  lrs_free_dat (Q);             /* deallocate lrs_dat */
  return points;
}

// This bit is to register the routine with R
static const R_CallMethodDef callMethods[] = {
  {"vertexenum", (DL_FUNC) &vertexenum, 5},
  {NULL, NULL, 0},
};

void R_init_vertexenum(DllInfo *info) {
  R_registerRoutines(info, NULL, callMethods, NULL, NULL);
}
