/* 
   Program generate triangulations of 3-manifolds by adding tetrahedra in 
   lexigraphic order.
*/

/*
  Written and maintained by Thom Sulanke (tsulanke@indiana.edu)

  See "Isomorphism-free lexicographic enumeration of triangulated surfaces and 
  3-manifolds" Thom Sulanke, Frank H. Lutz 
 */

/*
 Edited by Tair Akhmejanov to generate triangulations of normal 3-pseudomanifolds on 9 and 10 vertices.
 August 2011 (Cornell REU)
 */

#define VERSION "0.24"

/* use look-ahead to force additional tetrahedron to reduce choices. */
/* store two triangulations. _a for all added tetrahedra.  _p for all picked 
   tetrahedra. */

/* possible (mutually exclusive) compile macros
   MAX5  maximum edge degree is 5.
   NO66  edge degree is 5 or 6 and no face has two edges with edge degree 6.
   DODEC  NO66 requiring one vertex to have degree 12.
   NEIGHBORLY  all vertices are adjacent.
*/

#define USAGE \
" lextet [-v] [-h] [-i] [-o o] [-r res -m mod] nv"

#define HELPTEXT \
" lextet : generate triangulations of 3-manifolds with nv vertices.\n\
\n\
 help switches:\n\
   -h  show this text\n\
   -v  verbose output\n\
\n\
 parameter switches:\n\
   -i          if present only irreducible triangulations are generated\n\
   -r res      res for splitting\n\
   -m mod      mod for splitting\n\
\n\
   nv          number of vertices in generated triangulations.\n"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define CPUTIME 1          /* Whether to measure the cpu time or not */

#if CPUTIME
#include <sys/times.h>
#ifndef CLK_TCK
#include <time.h>
#endif
#endif

#define FALSE 0
#define TRUE 1

#define MAXN 200
#define MAXE 8400
#define MAXF MAXN*(MAXN-1)*(MAXN-2)/(3*2)
#define MAXT 8400

/* BIG macros taken from plantri. */
/* The program is so fast that the count of output graphs can quickly
   overflow a 32-bit integer.  Therefore, we use two long values
   for each count, with a ratio of 10^9 between them.  The macro
   ADDBIG adds a small number to one of these big numbers.  
   BIGTODOUBLE converts a big number to a double (approximately).
   SUMBIGS adds a second big number into a first big number.
   SUBBIGS subtracts a second big number from a first big number.
   PRINTBIG prints a big number in decimal.
   ZEROBIG sets the value of a big number to 0.
   ISZEROBIG tests if the value is 0.
   SETBIG sets a big number to a value at most 10^9-1.
   ISEQBIG tests if two big numbers are equal.
*/

typedef struct
{
    long hi,lo;
} bigint;

#define ZEROBIG(big) big.hi = big.lo = 0L
#define ISZEROBIG(big) (big.lo == 0 && big.hi == 0)
#define SETBIG(big,value) {big.hi = 0L; big.lo = (value);}
#define ADDBIG(big,extra) if ((big.lo += (extra)) >= 1000000000L) \
    { ++big.hi; big.lo -= 1000000000L;}
#define PRINTBIG(file,big) if (big.hi == 0) \
 fprintf(file,"%ld",big.lo); else fprintf(file,"%ld%09ld",big.hi,big.lo)
#define BIGTODOUBLE(big) (big.hi * 1000000000.0 + big.lo)
#define SUMBIGS(big1,big2) {if ((big1.lo += big2.lo) >= 1000000000L) \
    {big1.lo -= 1000000000L; big1.hi += big2.hi + 1L;} \
    else big1.hi += big2.hi;}
#define SUBBIGS(big1,big2) {if ((big1.lo -= big2.lo) < 0L) \
    {big1.lo += 1000000000L; big1.hi -= big2.hi + 1L;} \
    else big1.hi -= big2.hi;}
/* Note: SUBBIGS must not allow the value to go negative.
   SUMBIGS and SUBBIGS both permit big1 and big2 to be the same bigint. */
#define ISEQBIG(big1,big2) (big1.lo == big2.lo && big1.hi == big2.hi)


typedef struct
{
  int other_a[2];
  int type_a[2];  /* 0 = available, 1 = forced, 2 = picked, 
		   3 = forced then picked */
  int other_p[2];
} face;

#define AVAILABLE 0
#define FORCED 1
#define PICKED 2
#define FORCED_PICKED 3

typedef struct
{
  int mark;            /* for temporary use;
                          Only access mark via the MARK macros. */
} vert;

typedef struct
{
  int mark;            /* for temporary use;
                          Only access mark via the MARK macros. */
} oface;

static int markvalue = 30000;
#define RESETMARKS {int mki; if ((markvalue += 1) > 30000) \
       { markvalue = 1; for (mki=0;mki<2*maxnf;++mki) ofaces[mki].mark=0; \
         for (mki=0;mki<maxnv;++mki) verts[mki].mark=0;}}
#define MARK(e) (e)->mark = markvalue
#define ISMARKED(e) ((e)->mark >= markvalue)


static int maxEuler=0;

static int mcount =0;
static int num7 =0;
static int num8 =0;
static int num9 =0;
static int num10 =0;
static int num11 =0;

static int EulerChar;
static int E2;
static int E1;
static int E0;
//These variables represent the quantity of a given singularity type within one triangulation//
//t=orientable//
//k=non-orientable//
static int E0_t;
static int E0_k;
static int E91;
static int E91_t;
static int E91_k;
static int E92;
static int E92_t;
static int E92_k;
static int E93_t;
static int E93_k;

static face faces[MAXF];
static face *base[MAXN][MAXN][MAXN];

static vert verts[MAXN];
static vert *vertspt[MAXN];
static oface ofaces[2*MAXF];
static oface *ofacespt[MAXN][MAXN][MAXN];

static int verbose;
static int only_irreducible; /* flag if only irreducible triangulations are to
				be generated */
static int nv_a;     /* number of vertices in final triangulation */
static int ne_a;     /* number of edges in triangulation */
static int nf_a;     /* number of faces in triangulation */
static int nt_a;     /* number of tetrahedra in triangulation */
static int nv_p;     /* number of vertices in final triangulation */
static int ne_p;     /* number of edges in triangulation */
static int nf_p;     /* number of faces in triangulation */
static int nt_p;     /* number of tetrahedra in triangulation */
static int maxnv;  /* maximum number of vertices in a triangulation */
static int maxne;  /* maximum number of edges in a triangulation */
static int maxnf;  /* maximum number of faces in a triangulation */
static int maxnt;  /* maximum number of tetrahedra in a triangulation */

/* degreeMN is number of N-complexes containing M-complex, M < N */

static int degree01_a[MAXN]; /* edge degree of vertices, normal degree */
static int degree02_a[MAXN]; /* face degree at vertex */
static int degree03_a[MAXN]; /* tetrahedron degree of vertices, number of 
			     tetrahedra with that vertex */
static int degree12_a[MAXN][MAXN]; /* face degree around an edge 
				    = # of vertices in lk of edge */
static int degree13_a[MAXN][MAXN]; /* tetrahedron degree around an edge 
				    = # edge in lk of edge */
static int degree01_p[MAXN]; /* edge degree of vertices, normal degree */
static int degree02_p[MAXN]; /* face degree at vertex */
static int degree03_p[MAXN]; /* tetrahedron degree of vertices, number of 
			     tetrahedra with that vertex */
static int degree12_p[MAXN][MAXN]; /* face degree around an edge 
				    = # of vertices in lk of edge */
static int degree13_p[MAXN][MAXN]; /* tetrahedron degree around an edge 
				    = # edge in lk of edge */
static int complete_a[MAXN]; /* link of vertex is a triangulation of a sphere */
static int complete_p[MAXN]; /* link of vertex is a triangulation of a sphere */
static int completeness[MAXN]; /* 0 if not complete, 1 if newly complete, or 
				  2 if formerly complete */

static int match[MAXN][120][MAXN]; /* lk(v0) is equivalent to lk(0),
				      i is an index of the automorphisms of 
				      this equivalence,
				      v is mapped to match[v0][i][v] by the 
				      i-th automorphism */
static int nmatch[MAXN];   /* number of automorphisms above */
static int list_a[MAXT][4];  /* list of the vertices in each ordered 
			      tetrahedron as added to _a */
static int list_a_forced[MAXT]; /* the index of the picked tetrahedron which
				   forced this tetrahedron to be added; 
				   -1 if not forced */
static int list_p[MAXT][4];  /* list of the vertices in each ordered 
			      tetrahedron as added to _p */

static bigint ngenerated[MAXN]; /* number of triangulations generated by ne */
static bigint ngen_all; /* number of triangulations generated */
static int nt_match;        /* number of tetrahedra matched */
static int v_to_label[MAXN];/* relabeling of vertices */
static int label_to_v[MAXN];/* vertex with label*/
static int next_label;      /* next unused label */
static int debug_count;

static bigint ncalls_min_lex;
static int max_inter_nv;
static bigint closed_link[MAXN]; /* closed_link[i] = number of times i-th 
				    vertex link is closed */
static int prev_closed_link;
static int res,mod;        /* res/mod from command line (default 0/1) */
static char res_text[10];  /* text string for res with padded zeros */
static int splitlevel,
           splitcount;     /* used for res/mod splitting */

#define MAX(x,y) ((x)<(y) ? (y) : (x))
#define MIN(x,y) ((x)>(y) ? (y) : (x))

#ifdef SPLITTEST
static int splitcases;
#endif

void found_one();
void next_tetrahedron();

void error_exit(int errornum)
{
  fprintf(stderr,"Error number %d, exiting\n",errornum);
  exit(1);
}

static char i2a[52] = {
  'a','b','c','d','e','f','g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v','w','x','y','z',
  'A','B','C','D','E','F','G','H','I','J','K','L','M','N','O','P','Q','R','S','T','U','V','W','X','Y','Z'};

void write_lex(FILE *output)
{
  /* write out 3-manifold in sortable format.  
     one line of text for each 3-manifold.
     one character for each vertex of each tetrahedron. */

  int itet;
	
  if (nv_p <= 52) 
    for (itet=0; itet<nt_p; itet++)
      fprintf(output,"%c%c%c%c",
	      i2a[list_p[itet][0]],i2a[list_p[itet][1]],i2a[list_p[itet][2]],
	      i2a[list_p[itet][3]]);
  else
    for (itet=0; itet<nt_p; itet++)
      fprintf(output,"[%d,%d,%d,%d],\n",
	      list_p[itet][0]+1,list_p[itet][1]+1,list_p[itet][2]+1,
	      list_p[itet][3]+1);
	
  fprintf(output,"\n");
	
}


void dump_it()
{
  int ilist,nface;
  int v0,v1,v2;

  if (TRUE) {
    for (ilist=0; ilist<nt_a; ilist++)
      fprintf(stderr,"[%d,%d,%d,%d] ",
	      list_a[ilist][0]+1,list_a[ilist][1]+1,list_a[ilist][2]+1,
	      list_a[ilist][3]+1);
    fprintf(stderr,"\n");
    return;
  }

  fprintf(stderr,"\nnv_a = %d, ne_a = %d, nf_a = %d, nt_a = %d\n",
	  nv_a,ne_a,nf_a,nt_a);

  fprintf(stderr,"list of tetrahedra:\n");
  for (ilist=0; ilist<nt_a; ilist++)
    fprintf(stderr,"%2d %2d %2d %2d \n",
	    list_a[ilist][0],list_a[ilist][1],list_a[ilist][2],list_a[ilist][3]);

  fprintf(stderr,"edge matrix:\n");
  fprintf(stderr,"   |");
  for (v1=0; v1<nv_a; v1++) 
    fprintf(stderr,"%2d ",v1);
  fprintf(stderr,"\n");
  fprintf(stderr,"----");
  for (v1=0; v1<nv_a; v1++) 
    fprintf(stderr,"---");
  fprintf(stderr,"\n");
  for (v0=0; v0<nv_a; v0++) {
    fprintf(stderr,"%2d |",v0);
    for (v1=0; v1<nv_a; v1++) 
      if (degree12_a[v0][v1] != 0)
	fprintf(stderr," X ");
      else
	fprintf(stderr,"   ");
    fprintf(stderr,"\n");
  }

  nface = 0;
  fprintf(stderr,"face others:\n");
  for (v0=0; v0<nv_a-2; v0++)
    for (v1=v0+1; v1<nv_a-1; v1++)
      for (v2=v1+1; v2<nv_a; v2++)
	if (base[v0][v1][v2]->other_a[0] != -1) {
	  nface++;
	  fprintf(stderr,"(%d,%d,%d) %d %d\n",
		  v0,v1,v2,
		  base[v0][v1][v2]->other_a[0],base[v0][v1][v2]->other_a[1]);
	}

  fprintf(stderr,"edge degree:");
  for (v1=0; v1<nv_a; v1++) 
    fprintf(stderr,"%2d ",degree01_a[v1]);
  fprintf(stderr,"\n");

  fprintf(stderr,"face degree:");
  for (v1=0; v1<nv_a; v1++) 
    fprintf(stderr,"%2d ",degree02_a[v1]);
  fprintf(stderr,"\n");

  fprintf(stderr,"tetrahedron degree:");
  for (v1=0; v1<nv_a; v1++) 
    fprintf(stderr,"%2d ",degree03_a[v1]);
  fprintf(stderr,"\n");

  if (nface != nf_a) 
    error_exit(33);
}

void add_other_a(int v[3], int vo, int type)
{
  /* add vertex vo to base (v[0],v[1],v[2]) to make tetrahedron */

  int i;

  if (base[v[0]][v[1]][v[2]]->other_a[0] != -1) {
    base[v[0]][v[1]][v[2]]->other_a[1] = vo;
    base[v[0]][v[1]][v[2]]->type_a[1] = type;
  }
  else {
    base[v[0]][v[1]][v[2]]->other_a[0] = vo;
    base[v[0]][v[1]][v[2]]->type_a[0] = type;
    
    nf_a++;
    
    for (i=0; i<3; i++)
      degree02_a[v[i]]++;

    degree12_a[v[0]][v[1]]++;
    degree12_a[v[1]][v[0]]++;
    degree12_a[v[0]][v[2]]++;
    degree12_a[v[2]][v[0]]++;
    degree12_a[v[1]][v[2]]++;
    degree12_a[v[2]][v[1]]++;
  }
}

void add_other_p(int v[3], int vo)
{
  /* add vertex vo to base (v[0],v[1],v[2]) to make tetrahedron */

  int i;

  if (base[v[0]][v[1]][v[2]]->other_p[0] != -1)
    base[v[0]][v[1]][v[2]]->other_p[1] = vo;
  else {
    base[v[0]][v[1]][v[2]]->other_p[0] = vo;
    
    nf_p++;
    
    for (i=0; i<3; i++)
      degree02_p[v[i]]++;

    degree12_p[v[0]][v[1]]++;
    degree12_p[v[1]][v[0]]++;
    degree12_p[v[0]][v[2]]++;
    degree12_p[v[2]][v[0]]++;
    degree12_p[v[1]][v[2]]++;
    degree12_p[v[2]][v[1]]++;
  }
}

void add_tetrahedron_a(int v[4], int type)
{
  /* add a tetrahedron to 3-manifold */


  int i,j,vloc[7];

  for (i=0;i<4;i++)
    vloc[i] = v[i];
  for (i=0;i<3;i++)
    vloc[i+4] = v[i];

  /* check if previously forced */

  if (type == PICKED)
    if (base[vloc[0]][vloc[1]][vloc[2]]->other_a[0] == vloc[3] ||
	base[vloc[0]][vloc[1]][vloc[2]]->other_a[1] == vloc[3]) {
      for (i=0;i<4;i++)
	if (base[vloc[0+i]][vloc[1+i]][vloc[2+i]]->other_a[0] == vloc[3+i])
	  base[vloc[0+i]][vloc[1+i]][vloc[2+i]]->type_a[0] += PICKED;
	else
	  base[vloc[0+i]][vloc[1+i]][vloc[2+i]]->type_a[1] += PICKED;
      return;
    }
  
  /* update tetrahedron of faces (23) (12) */

  for (i=0;i<4;i++)
    add_other_a(vloc+i,vloc[3+i],type);

  /* update list of tetrahedra (03) */

  for (i=0;i<4;i++) {
    list_a[nt_a][i] = v[i];
    degree03_a[v[i]]++;
  }
  if (type == FORCED)
    list_a_forced[nt_a] = nt_p-1;
  else
    list_a_forced[nt_a] = -1;

  nt_a++;

  /* update nv */
  if(v[1] == nv_a){
	nv_a++;
  }	
  if (v[2] == nv_a)
    nv_a++;
  if (v[3] == nv_a)
    nv_a++;
  if (nv_a > max_inter_nv)
    max_inter_nv = nv_a;

  /* update degrees of vertices (01) and degrees of edges (13) */
  
  for (i=0;i<3;i++)
    for (j=i+1;j<4;j++) {
      if (degree13_a[v[i]][v[j]] == 0) {
	degree01_a[v[i]]++;
	degree01_a[v[j]]++;
	ne_a++;
      }
      degree13_a[v[i]][v[j]]++;
      degree13_a[v[j]][v[i]]++;
    }

  /* update complete */

  for (i=0;i<4;i++)
    if (2*degree02_a[v[i]] == 3*degree03_a[v[i]]) {
      complete_a[v[i]] = TRUE;
      completeness[v[i]] = 1;
    }
  
  //check_it();
}

void add_tetrahedron_p(int v[4], int type)
{	

  /* add a tetrahedron to 3-manifold */
  int i,j,vloc[7];

  if (type == PICKED) {
    
    /* update tetrahedron of faces (23) (12) */
    
    for (i=0;i<4;i++)
      vloc[i] = v[i];
    for (i=0;i<3;i++)
      vloc[i+4] = v[i];
    
    for (i=0;i<4;i++)
      add_other_p(vloc+i,vloc[3+i]);
    
    /* update list of tetrahedra (03) */
    
    for (i=0;i<4;i++) {
      list_p[nt_p][i] = v[i];
      degree03_p[v[i]]++;
    }
    nt_p++;
    
    /* update nv */
    if(v[1] == nv_p){
	nv_p++;
   }
	  if (v[2] == nv_p){
      nv_p++;
	  printf("added two new vertices \n");
	  }
    if (v[3] == nv_p)
      nv_p++;
    if (nv_p > max_inter_nv)
      max_inter_nv = nv_p;
    
    /* update degrees of vertices (01) and degrees of edges (13) */
    
    for (i=0;i<3;i++)
      for (j=i+1;j<4;j++) {
	if (degree13_p[v[i]][v[j]] == 0) {
	  degree01_p[v[i]]++;
	  degree01_p[v[j]]++;
	  ne_p++;
	}
	degree13_p[v[i]][v[j]]++;
	degree13_p[v[j]][v[i]]++;
      }
    
    /* update complete */
    //this condition still holds for any triangulated link that is a 2 manifold//
	//links of vertices in normal 3-pseudo-manifolds are 2 manifolds//
    for (i=0;i<4;i++)
      if (2*degree02_p[v[i]] == 3*degree03_p[v[i]])
	complete_p[v[i]] = TRUE;
  }  
  
  add_tetrahedron_a(v,type);
 	for (i=0; i<maxnv; i++) {
		v_to_label[i]=-1;
	}
	
  //check_it();

	
}

void remove_other_a(int v[3], int vo)
{
  /* remove vertex vo from base (v[0],v[1],v[2]) */
  
  int i;

  if (base[v[0]][v[1]][v[2]]->other_a[1] == vo) {
    base[v[0]][v[1]][v[2]]->other_a[1] = -1;
    base[v[0]][v[1]][v[2]]->type_a[1] = AVAILABLE;
  }
  else {
    base[v[0]][v[1]][v[2]]->other_a[0] = -1;
    base[v[0]][v[1]][v[2]]->type_a[0] = AVAILABLE;
    nf_a--;

    for (i=0; i<3; i++)
      degree02_a[v[i]]--;

    degree12_a[v[0]][v[1]]--;
    degree12_a[v[1]][v[0]]--;
    degree12_a[v[0]][v[2]]--;
    degree12_a[v[2]][v[0]]--;
    degree12_a[v[1]][v[2]]--;
    degree12_a[v[2]][v[1]]--;
  }
}

void remove_other_p(int v[3], int vo)
{
  /* remove vertex vo from base (v[0],v[1],v[2]) */
  
  int i;

  if (base[v[0]][v[1]][v[2]]->other_p[1] == vo) {
    base[v[0]][v[1]][v[2]]->other_p[1] = -1;
  }
  else {
    base[v[0]][v[1]][v[2]]->other_p[0] = -1;
    nf_p--;

    for (i=0; i<3; i++)
      degree02_p[v[i]]--;

    degree12_p[v[0]][v[1]]--;
    degree12_p[v[1]][v[0]]--;
    degree12_p[v[0]][v[2]]--;
    degree12_p[v[2]][v[0]]--;
    degree12_p[v[1]][v[2]]--;
    degree12_p[v[2]][v[1]]--;
  }
}

void remove_tetrahedron_a(int type, int v[4])
{
  int i,j;
  int vloc[7];

  for (i=0;i<4;i++)
    vloc[i] = v[i];
  for (i=0;i<3;i++)
    vloc[i+4] = v[i];
  
  if (type == PICKED)
    if ((base[v[0]][v[1]][v[2]]->other_a[0] == v[3] &&
	 base[v[0]][v[1]][v[2]]->type_a[0] == FORCED_PICKED) ||
	(base[v[0]][v[1]][v[2]]->other_a[1] == v[3] &&
	 base[v[0]][v[1]][v[2]]->type_a[1] == FORCED_PICKED)) {
      
      for (i=0;i<4;i++)
	if (base[vloc[i+0]][vloc[i+1]][vloc[i+2]]->other_a[0] == vloc[i+3])
	  base[vloc[i+0]][vloc[i+1]][vloc[i+2]]->type_a[0] = FORCED;
	else
	  base[vloc[i+0]][vloc[i+1]][vloc[i+2]]->type_a[1] = FORCED;
	
      return;
    }
  
  /* update list */
  
  nt_a--;

  /* update tetrahedron degrees of vertices (03) */

  for (i=0;i<4;i++) {
    degree03_a[v[i]]--;
    complete_a[v[i]] = FALSE;
    completeness[v[i]] = 0;
  }

  /* update nv */

  if (degree03_a[v[3]] == 0)
    nv_a--;
  if (degree03_a[v[2]] == 0)
    nv_a--;

  /* update degrees of vertices (01) and degrees of edges (13) */
  
  for (i=0;i<3;i++)
    for (j=i+1;j<4;j++) {
      degree13_a[v[i]][v[j]]--;
      degree13_a[v[j]][v[i]]--;
      if (degree13_a[v[i]][v[j]] == 0) {
	degree01_a[v[i]]--;
	degree01_a[v[j]]--;
	ne_a--;
      }
    }

  /* update tetrahedron of faces (23) (12) */

  for (i=0;i<4;i++)
    remove_other_a(vloc+i,vloc[i+3]);

  //check_it();
}

void remove_tetrahedron_p(int type)
{
  int i,j;
  int v[4],vloc[7];

  if (type == PICKED) {

    /* update list */
    
    nt_p--;
    
    for (i=0;i<4;i++)
      v[i] = list_p[nt_p][i];
    
  //printf("remove %d, %d, %d, %d \n",v[0],v[1],v[2],v[3]);
    /* update tetrahedron degrees of vertices (03) */
    
    for (i=0;i<4;i++) {
	degree03_p[v[i]]--;
	complete_p[v[i]] = FALSE;
    }
	
	
	  
    /* update nv */
    
    if (degree03_p[v[3]] == 0)
      nv_p--;
    if (degree03_p[v[2]] == 0)
      nv_p--;
    if(degree03_p[v[1]]==0){
      nv_p--;
      printf("deleted three vertices in one go \n");	
    }
    /* update degrees of vertices (01) and degrees of edges (13) */
    
    for (i=0;i<3;i++)
      for (j=i+1;j<4;j++) {
	degree13_p[v[i]][v[j]]--;
	degree13_p[v[j]][v[i]]--;
	if (degree13_p[v[i]][v[j]] == 0) {
	  degree01_p[v[i]]--;
	  degree01_p[v[j]]--;
	  ne_p--;
	}
      }
	  

	  
	
    /* update tetrahedron of faces (23) (12) */
    
    for (i=0;i<4;i++)
      vloc[i] = v[i];
    for (i=0;i<3;i++)
      vloc[i+4] = v[i];

    for (i=0;i<4;i++)
      remove_other_p(vloc+i,vloc[3+i]);

    while (list_a_forced[nt_a-1] == nt_p){
	printf("entered");
      remove_tetrahedron_a(FORCED,list_a[nt_a-1]);
    }
    remove_tetrahedron_a(PICKED,v);
  }
  else {
    remove_tetrahedron_a(FORCED,list_a[nt_a-1]);
  }

  //check_it();
}

void initialize()
{
  /* one time initialization */

  int v0,v1,v2,iface,lnv;

#ifdef SPLITTEST
  splitcases = 0;
#endif

  debug_count = 0;
  max_inter_nv = 0;
  ZEROBIG(ncalls_min_lex);

  for (lnv=0; lnv<MAXN; lnv++) {
    ZEROBIG(ngenerated[lnv]);
    ZEROBIG(closed_link[lnv]);
  }
  ZEROBIG(ngen_all);
  prev_closed_link = 0;

  iface = 0;
  for (v0=0; v0<maxnv-2; v0++)
    for (v1=v0+1; v1<maxnv-1; v1++)
      for (v2=v1+1; v2<maxnv; v2++) {
	base[v0][v1][v2] = &faces[iface];
	base[v0][v2][v1] = &faces[iface];
	base[v1][v0][v2] = &faces[iface];
	base[v1][v2][v0] = &faces[iface];
	base[v2][v0][v1] = &faces[iface];
	base[v2][v1][v0] = &faces[iface];

	ofacespt[v0][v1][v2] = &ofaces[2*iface];
	ofacespt[v1][v2][v0] = &ofaces[2*iface];
	ofacespt[v2][v0][v1] = &ofaces[2*iface];
	ofacespt[v0][v2][v1] = &ofaces[2*iface+1];
	ofacespt[v1][v0][v2] = &ofaces[2*iface+1];
	ofacespt[v2][v1][v0] = &ofaces[2*iface+1];

	iface++;
      }

  for (v0=0; v0<maxnv; v0++) {
    vertspt[v0] = &verts[v0];
  }
	
}

void initialize_first_edge(int degree0)

{

  int i,v0,v1,v2,v[4];

  /* clear data*/

  for (v0=0; v0<maxnv-2; v0++)
    for (v1=v0+1; v1<maxnv-1; v1++) 
      for (v2=v1+1; v2<maxnv; v2++) {
	base[v0][v1][v2]->other_a[0] = -1;
	base[v0][v1][v2]->other_a[1] = -1;
	base[v0][v1][v2]->type_a[0] = AVAILABLE;
	base[v0][v1][v2]->type_a[1] = AVAILABLE;
	base[v0][v1][v2]->other_p[0] = -1;
	base[v0][v1][v2]->other_p[1] = -1;
      }

  for (v0=0; v0<maxnv; v0++)
    for (v1=0; v1<maxnv; v1++) {
      degree12_a[v0][v1] = 0;
      degree13_a[v0][v1] = 0;
      degree12_p[v0][v1] = 0;
      degree13_p[v0][v1] = 0;
    }

  for (v0=0; v0<maxnv; v0++) {
    degree01_a[v0] = 0;
    degree02_a[v0] = 0;
    degree03_a[v0] = 0;
    degree01_p[v0] = 0;
    degree02_p[v0] = 0;
    degree03_p[v0] = 0;
    complete_a[v0] = FALSE;
    complete_p[v0] = FALSE;
  }

  for (v0=0; v0<maxnv; v0++)
    v_to_label[v0] = -1;

  nv_a = 3;
  ne_a = 0;
  nf_a = 0;
  nt_a = 0;
  nv_p = 3;
  ne_p = 0;
  nf_p = 0;
  nt_p = 0;

  /* add tetrahedra around first edge */

  for (i=0;i<4;i++)
    v[i] = i;
  add_tetrahedron_p(v,PICKED);
  for (i=4; i<degree0+2; i++) {
    v[2] = i-2;
    v[3] = i;
    add_tetrahedron_p(v,PICKED);
  }
  v[2] = degree0;
  add_tetrahedron_p(v,PICKED);
	
   int j;
} 

int mark_face_np(int *lnf, int *lnv, int *lnb, int v0, int v1, int v2, int v3)
{
  /* recursively mark the faces of the link of v0 adjacent to (v1,v2,v3) 
   across (v1,v3) and (v3,v2).
   update lnf, lnv, and lnb.
   if face is found with opposite orientation return TRUE.
 */

  int v4;

  if (!ISMARKED(vertspt[v3])) {
    MARK(vertspt[v3]);
    (*lnv)++;
  }

  if (base[v0][v1][v3]->other_a[0]==v2)
    v4 = base[v0][v1][v3]->other_a[1];
  else
    v4 = base[v0][v1][v3]->other_a[0];
  if (v4 == -1)
    (*lnb)++;
  else if (ISMARKED(ofacespt[v3][v1][v4])) 
    return TRUE;
  else if (!ISMARKED(ofacespt[v1][v3][v4])) {
    MARK(ofacespt[v1][v3][v4]);
    (*lnf)++;
    if (mark_face_np(lnf,lnv,lnb,v0,v1,v3,v4))
      return TRUE;
  }
  
  if (base[v0][v3][v2]->other_a[0]==v1)
    v4 = base[v0][v3][v2]->other_a[1];
  else
    v4 = base[v0][v3][v2]->other_a[0];
  if (v4 == -1)
    (*lnb)++;
  else if (ISMARKED(ofacespt[v2][v3][v4])) 
    return TRUE;
  else if (!ISMARKED(ofacespt[v3][v2][v4])) {
    MARK(ofacespt[v3][v2][v4]);
    (*lnf)++;
    if (mark_face_np(lnf,lnv,lnb,v0,v3,v2,v4))
      return TRUE;
  }

  return FALSE;
}

int nonplanar(int v0, int v1, int v2, int v3)
{
  /* return TRUE if we can figure out that the strongly connected component of
     the link of v0 containing (v1,v2,v3) is not planar.  
     here a sphere is also nonplanar.
  */
  /* for the strongly connected component containing (v1,v2,v3) of link of v0 
     after adding (v0,v1,v2,v3) count
     nf, nv, nb (= number of edges on boundary edges).
     also check that it is orientable.
  */

  int lnf,lnv,lnb;
  int v12,v31,v23;
  int nf_lnb;  /* number of faces required to fill in boundary */

  RESETMARKS;

  /* mark the faces around (v1,v2,v3) first since (v1,v2,v3) has not been added
     yet */

  lnf = 1;
  lnv = 3;
  lnb = 0;

  MARK(vertspt[v1]);
  MARK(vertspt[v2]);
  MARK(vertspt[v3]);

  v12 = base[v0][v1][v2]->other_a[0];
  if (v12 == -1)
    lnb++;
  else {
    lnf++;
    MARK(ofacespt[v1][v2][v12]);
  }

  v23 = base[v0][v2][v3]->other_a[0];
  if (v23 == -1)
    lnb++;
  else {
    lnf++;
    MARK(ofacespt[v2][v3][v23]);
  }

  v31 = base[v0][v3][v1]->other_a[0];
  if (v31 == -1)
    lnb++;
  else {
    lnf++;
    MARK(ofacespt[v3][v1][v31]);
  }

  if (v12 != -1)
    if (mark_face_np(&lnf,&lnv,&lnb,v0,v1,v2,v12))
      return TRUE;
  if (v23 != -1)
    if (mark_face_np(&lnf,&lnv,&lnb,v0,v2,v3,v23))
      return TRUE;
  if (v31 != -1)
    if (mark_face_np(&lnf,&lnv,&lnb,v0,v3,v1,v31))
      return TRUE;

  if (lnb == 0)
    return TRUE;
  nf_lnb = (lnb+2)/3;
  return (lnf + nf_lnb > 2*(lnv-2));
}


int admissable_vertex(int v0, int v1, int v2, int v3)
{
  /* check if adding (v0,v1,v2,v3) would cause the link of v0 to be 
     non-planar */

  int nv_v0, ne_v0, nf_v0;

  nv_v0 = degree01_a[v0];
  if (degree12_a[v0][v1] == 0)
    nv_v0++;
  if (degree12_a[v0][v2] == 0)
    nv_v0++;
  if (degree12_a[v0][v3] == 0)
    nv_v0++;

  nf_v0 = degree03_a[v0]+1;

  if (nf_v0 < 2*(nv_v0 - 2)) {
    
    /* check the 2D-connected component (after tetrahedron is added) */
    
    if (nonplanar(v0,v1,v2,v3))
      return FALSE;
    else
      return TRUE;
  }
  
  else {
    
    /* v0 should be complete */

    ne_v0 = degree02_a[v0];
    if (base[v0][v1][v2]->other_a[0] == -1)
      ne_v0++;
    if (base[v0][v1][v3]->other_a[0] == -1)
      ne_v0++;
    if (base[v0][v2][v3]->other_a[0] == -1)
      ne_v0++;
    if (2*ne_v0 == 3*nf_v0) {
      
      /* link of v0 has no boundary */
      /* link of v0 has Euler characteristic 2 */
      /* v0 is connected from tests when previous tetrahrdra were added */

      return TRUE;
    }

    return FALSE;
  }
}

int admissable_edge(int v0, int v1, int v2, int v3)
{
  /* check if adding (v0,v1,v2,v3) would cause the link of (v0,v1) to be 
     a cycle and at least one other edge */
  
  int va,vb,vc,vd;

  /* non pseudo-manifold conditions */
	//but these conditions remain the same for normal 3-pseudomanifolds//
	//link of each edge must still be 1-sphere (i.e. a cycle)//

  if (degree12_a[v0][v1] < 2)
    return TRUE;

  if (degree12_a[v0][v1] == degree13_a[v0][v1]+1)
    return TRUE;
  
  if (base[v0][v1][v2]->other_a[0] == -1)
    return TRUE;
  else
    va = base[v0][v1][v2]->other_a[0];
  
  if (base[v0][v1][v3]->other_a[0] == -1)
    return TRUE;
  else
    vb = base[v0][v1][v3]->other_a[0];
  
  vc = v2;
  while (va != vb && va != -1) {
    if (base[v0][v1][va]->other_a[0] == vc)
      vd = base[v0][v1][va]->other_a[1];
    else
      vd = base[v0][v1][va]->other_a[0];
    vc = va;
    va = vd;
  }
  
  if (va == vb)
    return FALSE;
  else
    return TRUE;
}

int smaller_lex()
{
  /* check if the relabeling starting at nt_match is lexigraphically 
     smaller than the current labeling */
  
  int label[4];        /* vertices of tetrahedron. also labels in relabeling */
  int w0,w1,w2,w3;      /* vertices of tetrahedron relabeled 
			   (label[0],label[1],label[2],label[3]) */
  int i;                /* vertex index for tetrahedron */
  int branch;           /* search might branch */
  int save_next_label;
  int save_nt_match;

  branch = FALSE;

  for (i=0; i<4; i++)
    label[i] = list_p[nt_match-1][i];
  
  while (nt_match<nt_p) {
    
    w3 = -1;
    while (w3 == -1) 

      /* label[0], label[1], label[2], and label[3] are the vertices of the 
	 nt_match-1 or better */
      
      if (label[0] == list_p[nt_match][0] && 
	  label[1] == list_p[nt_match][1] && 
	  label[2] == list_p[nt_match][2]) {
	
	/* current labeling has another tetrahedron with 
	   (label[0],label[1],label[2]). */
	
	/* find the next relabeled tetrahedron */
	
	w0 = label_to_v[label[0]];
	w1 = label_to_v[label[1]];
	
	if (label[2] == next_label) {
	  
	  /* try all possibilities of assigning next_label to unlabeled 
	     vertices */
	  
	  for (w2=0; w2<nv_a; w2++)
	    if (v_to_label[w2] == -1) 
	      if (base[w0][w1][w2]->other_a[0] != -1) {
		v_to_label[w2] = next_label;
		label_to_v[next_label] = w2;
		save_next_label = next_label;
		next_label++;
		save_nt_match = nt_match;
		if (smaller_lex())
		  return TRUE;
		for ( ; next_label>save_next_label; next_label--)
		  v_to_label[label_to_v[next_label-1]] = -1;
		nt_match = save_nt_match;
	      }
	  return FALSE;
	}
	
	w2 = label_to_v[label[2]];
	w3 = -1;
	
	if (base[w0][w1][w2]->other_a[0] == -1)
	  return FALSE;
	
	/* (w0,w1,w2) exists */
	
	if (base[w0][w1][w2]->other_a[1] != -1) {
	  
	  /* (w0,w1,w2) is complete */
	  
	  if (v_to_label[base[w0][w1][w2]->other_a[0]] > label[3] &&
	      v_to_label[base[w0][w1][w2]->other_a[1]] > label[3]) {
	    
	    /* both labels of other vertices could be next so pick smaller */
	    
	    if (v_to_label[base[w0][w1][w2]->other_a[0]] > 
		v_to_label[base[w0][w1][w2]->other_a[1]])
	      w3 = base[w0][w1][w2]->other_a[1];
	    else
	      w3 = base[w0][w1][w2]->other_a[0];
	  }
	  else if (v_to_label[base[w0][w1][w2]->other_a[0]] > label[3])
	    
	    /* one label of other vertices could be next so use it */
	    
	    w3 = base[w0][w1][w2]->other_a[0];
	  else if (v_to_label[base[w0][w1][w2]->other_a[1]] > label[3])
	    w3 = base[w0][w1][w2]->other_a[1];
	  else if (v_to_label[base[w0][w1][w2]->other_a[0]] == -1) {
	    if (v_to_label[base[w0][w1][w2]->other_a[1]] == -1)
	      
	      /* both final vertices of the tetrahedra of (w0,w1,w2) are 
		 unlabeled.  the search must branch below */
	      
	      branch = TRUE;
	    
	    /* first final vertex of the tetrahedra of (w0,w1,w2) is
	       unlabeled.  use it. */
	    
	    w3 = base[w0][w1][w2]->other_a[0];
	    v_to_label[w3] = next_label;
	    label_to_v[next_label] = w3;
	    next_label++;
	  }
	  else if (v_to_label[base[w0][w1][w2]->other_a[1]] == -1) {
	    
	    /* second final vertex of the tetrahedra of (w0,w1,w2) is only
	       unlabeled.  use it. */
	    
	    w3 = base[w0][w1][w2]->other_a[1];
	    v_to_label[w3] = next_label;
	    label_to_v[next_label] = w3;
	    next_label++;
	  }
	}
	else {
	  
	  /* (w0,w1,w2) exists but is not complete */
	  
	  if (v_to_label[base[w0][w1][w2]->other_a[0]] > label[3])
	    w3 = base[w0][w1][w2]->other_a[0];
	  else if (v_to_label[base[w0][w1][w2]->other_a[0]] == -1) {
	    w3 = base[w0][w1][w2]->other_a[0];
	    v_to_label[w3] = next_label;
	    label_to_v[next_label] = w3;
	    next_label++;
	  }
	}
	
	/* compare labels */
	
	if (w3 == -1)
	  return FALSE;
	if (v_to_label[w3] > list_p[nt_match][3])
	  return FALSE;
    if (v_to_label[w3] < list_p[nt_match][3])
	  return TRUE;

	/* current labeling and relabeling both have another tetrahedron 
	   with (label[0],label[1],label[2]).  they are the same. */
	
	if (branch) {
	  save_nt_match = nt_match;
	  nt_match++;
	  save_next_label = next_label-1;
	  if (smaller_lex())
	    return TRUE;
	  for ( ; next_label>save_next_label; next_label--)
	    v_to_label[label_to_v[next_label-1]] = -1;
	  nt_match = save_nt_match;
	  branch = FALSE;
	  w3 = base[w0][w1][w2]->other_a[1];
	  v_to_label[w3] = next_label;
	  label_to_v[next_label] = w3;
	  next_label++;
	}
	  
	label[3] = v_to_label[w3];
      }
    
      else {
	
	/* current labeling does not have another tetrahedron with 
	   (label[0],label[1],label[2]). */
	
	/* find the next relabeled tetrahedron */
	
	w0 = label_to_v[label[0]];
	w1 = label_to_v[label[1]];
	w3 = -1;
	
	if (label[2] == next_label) {
	  
	  /* try all possibilities of assigning next_label to unlabeled 
	     vertices */
	  
	  for (w2=0; w2<nv_a; w2++)
	    if (v_to_label[w2] == -1) 
			if (base[w0][w1][w2]->other_a[0] != -1){
				//printf("TRUE1\n");
				return TRUE;}
	}
	else {
	  
	  w2 = label_to_v[label[2]];
	  
	  if (base[w0][w1][w2]->other_a[0] != -1) {
	    
	    /* (w0,w1,w2) exists */
	    
	    if (v_to_label[base[w0][w1][w2]->other_a[0]] > label[3] ||
			v_to_label[base[w0][w1][w2]->other_a[0]] == -1)
			return TRUE;
	    
	    if (base[w0][w1][w2]->other_a[1] != -1)
	      if (v_to_label[base[w0][w1][w2]->other_a[1]] > label[3] ||
			  v_to_label[base[w0][w1][w2]->other_a[1]] == -1)
			  return TRUE;
	  }
	}
	
	/* neither current labeling nor relabeling have another tetrahedron 
	   with (label[0],label[1],label[2]). increase this 3-tuple */
	
	label[2]++;
	if (label[2] == next_label+1 ||
	    label[2] == nv_a-1) {
	  label[1]++;
	  if (label[1] == next_label ||
	      label[1] == nv_a-2) {
	    label[0]++;
	    label[1] = label[0] + 1;
	  }
	  label[2] = label[1] + 1;
	}
	label[3] = label[2];
      }
    
    nt_match++;
  }
  
  /* they are the same */
  
  return FALSE;
}

int min_lex()
{
  /* check that the current labeling of the list of tetrahedra is 
     lexigraphical minimum */

  int v0,v1,v;
  int ineighbor,ioffset,save;
  int neighbor[MAXN];
  int save_next_label;
  int imatch;

  ADDBIG(ncalls_min_lex,1);

  save_next_label = degree12_a[0][1]+1+1;

  for (v0=0; v0<nv_a; v0++) {
    if (completeness[v0] == 1)
      nmatch[v0] = 0;

    if (completeness[0] != 2 || completeness[v0] != 2) {
      for (v1=0; v1<nv_a; v1++) 
	if (v1 != v0)
	  if (degree13_a[v0][v1] == degree13_a[0][1] &&
	      degree13_a[v0][v1] == degree12_a[v0][v1]) {
		  
	    /* make a list of the neighbors of (v0,v1) */
	    
	    for (v=0; (v==v0||v==v1?TRUE:base[v0][v1][v]->other_a[0] == -1); v++)
	      {}
	    neighbor[0] = v;
	    neighbor[1] = base[v0][v1][v]->other_a[0];
	    for (ineighbor=2; ineighbor<degree12_a[0][1]; ineighbor++)
	      if (base[v0][v1][neighbor[ineighbor-1]]->other_a[0] == 
		  neighbor[ineighbor-2])
		neighbor[ineighbor] = 
		  base[v0][v1][neighbor[ineighbor-1]]->other_a[1];
	      else
		neighbor[ineighbor] = 
		  base[v0][v1][neighbor[ineighbor-1]]->other_a[0];
	    
	    /* set the initial values of v_to_label for (v0,v1) */
	    
	    v_to_label[v0] = 0;
	    label_to_v[0] = v0;
	    v_to_label[v1] = 1;
	    label_to_v[1] = v1;
	    v_to_label[v] = 2;
	    label_to_v[2] = v;
	    for (ioffset=1; ioffset<=degree12_a[0][1]/2; ioffset++) {
	      v_to_label[neighbor[ioffset]] = 2*ioffset+1;
	      label_to_v[2*ioffset+1] = neighbor[ioffset];
	    }
	    for (ioffset=1; ioffset<(degree12_a[0][1]+1)/2; ioffset++) {
	      v_to_label[neighbor[-ioffset+degree12_a[0][1]]] = 2*ioffset+1+1;
	      label_to_v[2*ioffset+1+1] = neighbor[-ioffset+degree12_a[0][1]];
	    }
	    for (ineighbor=0; ineighbor<degree12_a[0][1]; ineighbor++) {
	      
	      /* check starting at each neighbor of (v0,v1) going clockwise */
	      
	      nt_match = degree12_a[0][1];
	      next_label = save_next_label;
	      if (smaller_lex()) {
		for ( ; next_label>0; next_label--)
		  v_to_label[label_to_v[next_label-1]] = -1;
		return FALSE;
	      }

	      for ( ; next_label>save_next_label; next_label--)
		v_to_label[label_to_v[next_label-1]] = -1;
	      if (completeness[v0] == 1)
		if (nt_match >= degree03_a[0]) {
		  for (v=0; v<=degree01_a[0]; v++)
		    match[v0][nmatch[v0]][v] = label_to_v[v];
		  nmatch[v0]++;
		}
	      
	      /* rotate the labeling for next neighbor */
	      
	      save = v_to_label[neighbor[degree12_a[0][1]-1]];
	      for (ioffset=degree12_a[0][1]-1; ioffset>0; ioffset--) {
		v_to_label[neighbor[ioffset]] = 
		  v_to_label[neighbor[ioffset-1]];
		label_to_v[v_to_label[neighbor[ioffset]]] = neighbor[ioffset];
	      }
	      v_to_label[neighbor[0]] = save;
	      label_to_v[v_to_label[neighbor[0]]] = neighbor[0];
	    }
	    
	    /* flip the labeling for counterclockwise check */
	    
	    for (ioffset=1; ioffset<(degree12_a[0][1]+1)/2; ioffset++) {
	      save = v_to_label[neighbor[ioffset]];
	      v_to_label[neighbor[ioffset]] = 
		v_to_label[neighbor[-ioffset+degree12_a[0][1]]];
	      label_to_v[v_to_label[neighbor[ioffset]]] = neighbor[ioffset];
	      v_to_label[neighbor[-ioffset+degree12_a[0][1]]] = save;
	      label_to_v[v_to_label[neighbor[-ioffset+degree12_a[0][1]]]] = 
		neighbor[-ioffset+degree12_a[0][1]];
	    }
	    
	    for (ineighbor=0; ineighbor<degree12_a[0][1]; ineighbor++) {
	      
	      /* check starting at each neighbor of (v0,v1) going 
		 counterclockwise */
	      
	      nt_match = degree12_a[0][1];
	      next_label = save_next_label;
	      if (smaller_lex()) {
		for ( ; next_label>0; next_label--)
		  v_to_label[label_to_v[next_label-1]] = -1;
		return FALSE;
	      }
	      
	      for ( ; next_label>save_next_label; next_label--)
		v_to_label[label_to_v[next_label-1]] = -1;
	      if (completeness[v0] == 1)
		if (nt_match >= degree03_a[0]) {
		  for (v=0; v<=degree01_a[0]; v++)
		    match[v0][nmatch[v0]][v] = label_to_v[v];
		  nmatch[v0]++;
		}
	      
	      /* rotate the labeling for next neighbor */
	      
	      save = v_to_label[neighbor[degree12_a[0][1]-1]];
	      for (ioffset=degree12_a[0][1]-1; ioffset>0; ioffset--) {
		v_to_label[neighbor[ioffset]] = 
		  v_to_label[neighbor[ioffset-1]];
		label_to_v[v_to_label[neighbor[ioffset]]] = neighbor[ioffset];
	      }
	      v_to_label[neighbor[0]] = save;
	      label_to_v[v_to_label[neighbor[0]]] = neighbor[0];
	    }
	    
	    /* undo labeling before next (v0,v1) or returning */
	    
	    for ( ; next_label>0; next_label--)
	      v_to_label[label_to_v[next_label-1]] = -1;
	  }
    }
    
    else if (nmatch[v0] != 0) {
      
      /* completeness[0] == 2 && completeness[v0] == 2 
	 and lk(0) is equivalent to lk(v0) */
      
      for (imatch=0; imatch<nmatch[v0]; imatch++) {
	for (v=0; v<=degree01_a[0]; v++) {
	  label_to_v[v] = match[v0][imatch][v];
	  v_to_label[label_to_v[v]] = v;
	}
	nt_match = degree03_a[0];
	next_label = degree01_a[0] + 1;
	if (smaller_lex()) {
	  for ( ; next_label>0; next_label--)
	    v_to_label[label_to_v[next_label-1]] = -1;
	  return FALSE;
	}
	for ( ; next_label>degree01_a[0]+1; next_label--)
	  v_to_label[label_to_v[next_label-1]] = -1;
      }
      for ( ; next_label>0; next_label--)
	v_to_label[label_to_v[next_label-1]] = -1;
    }

    if (complete_p[0] && completeness[v0] == 1)
      completeness[v0] = 2;
    
  }

  return TRUE;
}

int contractible(int v0, int v1)
{
  /* check to see if the edge (v0,v1) is contractible.  vertices v0 and v1 are
     complete. */

  int v2,v3;
  int neighbors;  /* number of common neighbors of v0 and v1 */
  int eneighbors;  /* number of common neighboring edges of v0 and v1 */

  neighbors = 0;
  eneighbors = 0;
  for (v2=0; v2<nv_a; v2++)
    if (v2!=v0 && v2!=v1)
      if (degree12_a[v0][v2] != 0 && degree12_a[v1][v2] != 0) {
	neighbors++;
	if (neighbors == degree12_a[v0][v1]+1)
	  return FALSE;
	for (v3=v2+1; v3<nv_a; v3++)
	  if (v3!=v0 && v3!=v1)
	    if (base[v0][v2][v3]->other_a[0] != -1 && 
		base[v1][v2][v3]->other_a[0] != -1) {
	      eneighbors++;
	      if (eneighbors == degree12_a[v0][v1]+1)
		return FALSE;
	    }
      }
  return TRUE;
}

void found_one()
{
  /* found a triangulation */

  char outfilename[100];
	FILE *file;
  ADDBIG(ngenerated[nv_a],1);
  ADDBIG(ngen_all,1);
	
	if (nv_p==maxnv) {

			sprintf(outfilename,"3-manifolds_%dv_%d_%d_%d_%d_%d_%d_%d_%d_%d_%d_Eul%d.lex%c",nv_p,E2,E1,E0_t,E0_k,E91_t,E91_k,E92_t,E92_k,E93_t,E93_k,EulerChar,0);
			if ((file = fopen(outfilename,"a")) == NULL)
			{
				fprintf(stderr,"can't open %s for writing\n",outfilename);
				exit(1);
			}
		
		write_lex(file);
		fflush(file);
		fclose(file);
	}
	
 /*//the way the file writing originally was//
  if (TRUE) {
    
    if (outfile_lex[nv_a][E2][E1][E0_t][E0_k][E91_t][E91_k][E92_t][E92_k][EulerChar] == NULL) {
		sprintf(outfilename,"3-manifolds_%d_%d_%d_%d_%d_%d_%d_%d_%d_Eul%d.lex%c",nv_a,E2,E1,E0_t,E0_k,E91_t,E91_k,E92_t,E92_k,EulerChar,0);
		//sprintf(outfilename,"3-manifolds_v%d_r%s_m%d.lex%c",nv_a,res_text,mod,0);
		if ((outfile_lex[nv_a][E2][E1][E0_t][E0_k][E91_t][E91_k][E92_t][E92_k][EulerChar] = fopen(outfilename,"w")) == NULL)
		{
				fprintf(stderr,"can't open %s for writing\n",outfilename);
		exit(1);
		}
    }
    
    write_lex(outfile_lex[nv_a][E2][E1][E0_t][E0_k][E91_t][E91_k][E92_t][E92_k][EulerChar]);
    fflush(outfile_lex[nv_a][E2][E1][E0_t][E0_k][E91_t][E91_k][E92_t][E92_k][EulerChar]);
  }
  */
}

int force_tetrahedron(int v[4])
{
  /* check if the just added tetrahedron forces additional tetrahedra to be
     added.
     if forced tetrahedron lead to a conflict, return FALSE.  
  */

  /* no conflict */
  
  return TRUE;
}

//determines the rank of homology//
int homRank(int vi)
{
	
	int b;
	int c;
	int d;
	int e;
	int tetras[nt_p];
	int counter;
	int counter1;
	int flag;
	int flag1;
	int seenit;
	int loop;
	int loop1;
	int linkDeg = degree01_p[vi];;
	
	counter=0;
	int a;
	
	for (a=0; a<nt_p; a++) {
		tetras[a]=-1;
	}
	
	//get all tetrahedra that have vi in it//
	a=0;
	while(a<nt_p) {
		flag=0;
		for (b=0; b<4; b++) {
			if (list_p[a][b]==vi) {
				flag=1;
			}
		}
		//if vi is in this tetrahedron then//
		if (flag==1) {
			tetras[counter]=a;
			counter=counter+1;
		}
		a++;
	}
	
	
	int linkVs[counter][nv_p];
	int vertex;
	
	
	for (loop1=0; loop1<counter; loop1++) {
		for (loop=0; loop<nv_p; loop++) {
			linkVs[loop1][loop]=-1;
		}
	}
	
	for (a=0; a<counter; a++) {
		vertex=0;
		for(b=0;b<4;b++){
			if(list_p[tetras[a]][b]!=vi){
				linkVs[a][vertex]=list_p[tetras[a]][b];
				vertex++;
			}
		}
	}
	
	int edges[3*counter][2];
	int faces[counter][3];
	
	//fill the faces//
	for (a=0; a<counter; a++) {
		for (b=0; b<3; b++) {
			faces[a][b]=linkVs[a][b];
		}
	}
	
	
	//This part is to determine orientability of the linked surface.//
	int edgeV;
	int edgeCount;
	int newEdge;
	int v1;
	int v2;
	edgeCount=0;
	
	//get all of the edges//
	for (a=0; a<counter; a++) {
		for (b=0; b<3; b++) {
			newEdge=1;
			
			if (b==0) {
				v1=1;
				v2=2;
			}
			if (b==1) {
				v1=0;
				v2=2;
			}
			if (b==2) {
				v1=0;
				v2=1;
			}
			
			for (c=0; c<edgeCount; c++) {
				//the second part of this -or- should not really happen i.e. vertices arleady ordered smallest to greatest//
				//but just in case//
				if ((edges[c][0]==faces[a][v1] && edges[c][1]==faces[a][v2]) || (edges[c][0]==faces[a][v2] && edges[c][1]==faces[a][v1])) {
					newEdge=0;
				}
			}
			
			if(newEdge==1){
				edgeV=0;
				for (c=0; c<3; c++) {
					if (c!=b) {
						edges[edgeCount][edgeV]=faces[a][c];
						edgeV++;
					}
				}
				edgeCount++;
			}
		}
	}
	
	
	
	int homol[edgeCount][counter];
	for (a=0; a<counter; a++) {//for every face//
		for (b=0; b<edgeCount; b++) {//for every edge//
			//for (c=0; c<3; c++) {//for every vertex in face//
			if((edges[b][0]==faces[a][0] && edges[b][1]==faces[a][1]) || (edges[b][1]==faces[a][0] && edges[b][0]==faces[a][1])){
				homol[b][a]=1;
			} 
			else if((edges[b][0]==faces[a][1] && edges[b][1]==faces[a][2]) || (edges[b][1]==faces[a][1] && edges[b][0]==faces[a][2])){
				homol[b][a]=1;					
			}
			else if((edges[b][0]==faces[a][0] && edges[b][1]==faces[a][2]) || (edges[b][1]==faces[a][0] && edges[b][0]==faces[a][2])){
				homol[b][a]=-1;
			}
			else{
				homol[b][a]=0;
			}
			//}
		}
	}
	
	
	int zeroColumn;
	int pivot;
	double pivotVal;
	pivot=0;
	int tempRow[counter];
	double difFactor;
	
	for (a=0; a<counter; a++) {//for every column//
		//is it a zero column//
		zeroColumn=1;
		for (b=pivot; b<edgeCount; b++) {
			if (homol[b][a]!=0) {
				zeroColumn=0;
			}
		}
		if (!zeroColumn) {
			if (homol[pivot][a]==0) {
				c=pivot;
				while (homol[c][a]==0) {
					c++;
				}
				
				for (d=0; d<counter; d++) {
					tempRow[d]=homol[pivot][d];
					homol[pivot][d]=homol[c][d];
					homol[c][d]=tempRow[d];
				}
			}
			pivotVal=homol[pivot][a];
			
			
			for (b=pivot+1; b<edgeCount; b++) {
				difFactor = homol[b][a]/pivotVal;
				for (d=a; d<counter; d++) {
					homol[b][d]=(homol[b][d]-(difFactor*homol[pivot][d]));
				}
			}
		}
		
		pivot++;
		
	}
	
	int zeroRows;
	int allZeros;
	zeroRows=0;
	for (b=0; b<edgeCount; b++) {
		allZeros=1;
		for (a=0; a<counter; a++) {
			if (homol[b][a]!=0) {
				//printf("not a zero row: %d\n", b);
				allZeros=0;
			}
		}
		if (allZeros) {
			zeroRows++;
		}
	}
	int rank;
	rank=edgeCount-zeroRows;
	
	
	int Dim;
	Dim = counter - rank;

	return(Dim);
	
	//Part to determine orientability of the surface is over//	
}

//checks that the link of a vertex is connected//
int link_connected(int vi){

	
	int b;
	int c;
	int d;
	int e;
	int tetras[nt_p];
	int counter;
	int counter1;
	int flag;
	int flag1;
	int seenit;
	int loop;
	int loop1;
	int linkDeg = degree01_p[vi];;
	
	counter=0;
	int a;
	
	for (a=0; a<nt_p; a++) {
		tetras[a]=-1;
	}
	
	//get all tetrahedra that have vi in it//
	a=0;
	while(a<nt_p) {
		flag=0;
		for (b=0; b<4; b++) {
			if (list_p[a][b]==vi) {
				flag=1;
			}
		}
		//if vi is in this tetrahedron then//
		if (flag==1) {
			tetras[counter]=a;
			counter=counter+1;
		}
		a++;
	}
	
	
	int linkVs[counter][nv_p];
	int vertex;
	
	
	for (loop1=0; loop1<counter; loop1++) {
		for (loop=0; loop<nv_p; loop++) {
			linkVs[loop1][loop]=-1;
		}
	}
	
	for (a=0; a<counter; a++) {
		vertex=0;
		for(b=0;b<4;b++){
			if(list_p[tetras[a]][b]!=vi){
				linkVs[a][vertex]=list_p[tetras[a]][b];
				vertex++;
			}
		}
	}

	int edges[3*counter][2];
	int faces[counter][3];
	
	//fill the faces//
	for (a=0; a<counter; a++) {
		for (b=0; b<3; b++) {
			faces[a][b]=linkVs[a][b];
		}
	}
	
	
	//checking links of all vertices in the link of vi//
	//i.e. links of links//
	int linkSend[counter][nv_p];
	int vSend;
	int init;
	int newCount;
	int tetCount;
	int vDeg;
	int inbag;
	int linkVertex;
	int linkVertexA;
	
	for (vSend=0; vSend<nv_p; vSend++) {
		linkVertex=0;
		
		for (c=0; c<counter; c++) {
			for (d=0; d<nv_p; d++) {
				if (vSend==linkVs[c][d]) {
					linkVertex=1;
				}
			}
		}
		
		if(vSend!=vi && linkVertex==1){
		
		vDeg=0;
		for (a=0; a<nv_p; a++) {
			inbag=0;
			for (c=0; c<counter; c++) {
				linkVertexA=0;
				for (d=0; d<nv_p; d++) {
					if (vSend==linkVs[c][d]) {
						linkVertexA=1;
					}
				}
				if (linkVertexA==1) {
					for (d=0; d<nv_p; d++) {
						if (a==linkVs[c][d]) {
							inbag=1;
						}
					}
				}
			}
			
			if (inbag==1) {
				if((degree13_p[vSend][a]>0) && (vSend!=a) && (a!=vi)){
					vDeg++;
				}
			}
		}
			
		tetCount=0;
		for (a=0; a<counter; a++) {
			for (b=0; b<nv_p; b++) {
				linkSend[a][b]=-1;
			}
		}
		//is vSend a vertex in the link of vi//
		for (a=0; a<counter; a++) {
			init =0;
			newCount=0;
			for(b=0;b<4;b++){
				if(linkVs[a][b]==vSend){
					init=1;
				}
			}
			if(init==1){
				for (b=0; b<4; b++) {
					if(linkVs[a][b]!=vSend && linkVs[a][b]!=-1 /*&& degree13_p[vSend][linkVs[a][b]]>0*/){
						if (degree13_p[vSend][linkVs[a][b]]<=0) {
							printf("degree wrong\n");
							exit(1);
						}
						linkSend[tetCount][newCount]=linkVs[a][b];
						newCount++;
					}
				}
				tetCount++;
			}
		}
		if (tetCount!=0) {
			//printf("sending vDeg: %d\n", vDeg);
			if(!linkOfLink_connected(vSend, linkSend, tetCount, vDeg)){
				printf("link of a link not connected!\n");
				exit(1);
				return FALSE;
			}
		}
		}
	}
	
	
	
	int newOne;
	newOne=3;
	int connected;
	int repeat;
	
	for(a=0; a<nv_p; a++){
		if(linkVs[0][a]!=-1){
			for (b=1; b<counter; b++) {
				connected = 0;
				for(c=0;c<4;c++){
					if (linkVs[0][a]==linkVs[b][c]) {
						connected = 1;
					}
				}
				if(connected==1){
					for(d=0;d<4;d++){
						if (linkVs[b][d]!=vi && linkVs[b][d]!=-1) {
							repeat = 0;
							for (e=0; e<newOne; e++) {
								if(linkVs[0][e]==linkVs[b][d]){
									repeat=1;
								}
							}
							if (repeat==0) {
								linkVs[0][newOne]=linkVs[b][d];
								newOne++;
							}
						}
					}
				}
			}
		}
	}
	
	int final =0;
	for (a=0; a<nv_p; a++) {
		if (linkVs[0][a]!=-1) {
			final++;
		}
	}
	
	if (newOne==linkDeg) {
		return TRUE;
	}
	else{
		return FALSE;
	}
	
}

int linkOfLink_connected(int vi, int linkVs[nt_p][nv_p], int counter, int linkDeg){
	//counter is the number of tetrahedras i.e. linkVs[counter][nv_p]//
	
	int b;
	int c;
	int d;
	int e;
	int tetras[nt_p];
	int counter1;
	int flag;
	int flag1;
	int seenit;
	int loop;
	int loop1;
	
	int a;
	
	int newOne;
	int connected;
	int repeat;
	
	
	
	newOne=0;
	int firstNonEmptyTet;
	firstNonEmptyTet=-1;
	while(newOne==0){
		firstNonEmptyTet++;
		for (a=0; a<nv_p; a++) {
			if(linkVs[firstNonEmptyTet][a]!=-1){
				newOne++;
			}
		}
	}
	
	if (newOne!=2) {
		printf("newOne!=2\n");
		exit(1);
	}
	
	for(a=0; a<nv_p; a++){
		if(linkVs[firstNonEmptyTet][a]!=-1){
			for (b=1; b<counter; b++) {
				connected = 0;
				for(c=0;c<4;c++){
					if (linkVs[firstNonEmptyTet][a]==linkVs[b][c]) {
						connected = 1;
					}
				}
				if(connected==1){
					for(d=0;d<4;d++){
						if (linkVs[b][d]!=vi && linkVs[b][d]!=-1) {
							repeat = 0;
							for (e=0; e<newOne; e++) {
								if(linkVs[firstNonEmptyTet][e]==linkVs[b][d]){
									repeat=1;
								}
							}
							if (repeat==0) {
								linkVs[firstNonEmptyTet][newOne]=linkVs[b][d];
								newOne++;
							}
						}
					}
				}
			}
		}
	}
	
	int final =0;
	for (a=0; a<nv_p; a++) {
		if (linkVs[firstNonEmptyTet][a]!=-1) {
			final++;
		}
	}
	
	if (newOne==linkDeg) {
		return TRUE;
	}
	else{
		return FALSE;
	}
	
}

//this function is never called in the final version//
//just used for debugging purposes//
int link_connectedEdge(int vi,int vj){
	
	
	int b;
	int c;
	int d;
	int e;
	int tetras[nt_p];
	int counter;
	int counter1;
	int flag;
	int flag1;
	int seenit;
	int loop;
	int loop1;
	int linkDeg = degree12_p[vi][vj];
	
	counter=0;
	int a;
	
	for (a=0; a<nt_p; a++) {
		tetras[a]=-1;
	}
	
	//get all tetrahedra that have vi in it//
	a=0;
	while(a<nt_p) {
		flag=0;
		for (b=0; b<4; b++) {
			if (list_p[a][b]==vi) {
				for (c=0; c<4; c++) {
					if(list_p[a][c]==vj){
						flag=1;
					}
				}
			}
		}
		//if vi is in this tetrahedron then//
		if (flag==1) {
			tetras[counter]=a;
			counter=counter+1;
		}
		a++;
	}
	
	
	int linkVs[counter][nv_p];
	int vertex;
	
	
	for (loop1=0; loop1<counter; loop1++) {
		for (loop=0; loop<nv_p; loop++) {
			linkVs[loop1][loop]=-1;
		}
	}
	
	for (a=0; a<counter; a++) {
		vertex=0;
		for(b=0;b<4;b++){
			if(list_p[tetras[a]][b]!=vi && list_p[tetras[a]][b]!=vj){
				linkVs[a][vertex]=list_p[tetras[a]][b];
				vertex++;
			}
		}
	}
	
	
	
	int newOne;
	newOne=2;
	int connected;
	int repeat;
	
	for(a=0; a<nv_p; a++){
		if(linkVs[0][a]!=-1){
			for (b=1; b<counter; b++) {
				connected = 0;
				for(c=0;c<4;c++){
					if (linkVs[0][a]==linkVs[b][c]) {
						connected = 1;
					}
				}
				if(connected==1){
					for(d=0;d<4;d++){
						if (linkVs[b][d]!=vi && linkVs[b][d]!=vj && linkVs[b][d]!=-1) {
							repeat = 0;
							for (e=0; e<newOne; e++) {
								if(linkVs[0][e]==linkVs[b][d]){
									repeat=1;
								}
							}
							if (repeat==0) {
								linkVs[0][newOne]=linkVs[b][d];
								newOne++;
							}
						}
					}
				}
			}
		}
	}
	
	int final =0;
	for (a=0; a<nv_p; a++) {
		if (linkVs[0][a]!=-1) {
			final++;
		}
	}
	
	if (newOne==linkDeg) {
		return TRUE;
	}
	else{
		return FALSE;
	}
	
}



int do_tetrahedron(int v[4], int type)
{
  int done;
  int vi;
	int vj;
  int i,j,check_vi;
  int vloc[7];

  for (i=0;i<4;i++)
    vloc[i] = v[i];
  for (i=0;i<3;i++)
    vloc[i+4] = v[i];
	
  /* add a new tetrahedron and check pruning conditions. */

  /* check if new picked tetrahedron was previously forced */

  if (type == PICKED && (base[v[0]][v[1]][v[2]]->other_a[0] == v[3] || base[v[0]][v[1]][v[2]]->other_a[1] == v[3])) {
	  add_tetrahedron_p(v,type);
    if (!min_lex()) {
      remove_tetrahedron_p(type);
      return FALSE;
    }
  }
  else {

    /* pruning before adding tetrahedron */
    
    /* check if addition of tetrahedron is blocked by forced tetrahedra */
    
    if (type == PICKED)
      for (i=0; i<4; i++)
		  if (base[vloc[i+0]][vloc[i+1]][vloc[i+2]]->other_a[1] != -1)
			  if (base[vloc[i+0]][vloc[i+1]][vloc[i+2]]->other_a[0] != vloc[i+3] && base[vloc[i+0]][vloc[i+1]][vloc[i+2]]->other_a[1] != vloc[i+3]){
				  return FALSE;}
    
    /* check if link of vertex or link of edge is already complete */

    for (i=0; i<4; i++)
		if (complete_a[v[i]]){
		  //printf("pruning3 \n");

			return FALSE;}
    for (i=0; i<4-1; i++)
      for (j=i+1; j<4; j++) 
		  if (degree12_a[v[i]][v[j]] != 0 && (degree12_a[v[i]][v[j]] == degree13_a[v[i]][v[j]])){
			  //printf("pruning4 \n");

			  return FALSE;}

    /* check that adding tetrahedron would not cause the link of (v[i],v[j]) 
       to be a cycle and at least one other edge */
    
    if (!admissable_edge(v[0],v[1],v[2],v[3]))
      return FALSE;
    if (!admissable_edge(v[0],v[2],v[1],v[3]))
      return FALSE;
    if (!admissable_edge(v[0],v[3],v[1],v[2]))
      return FALSE;
    if (!admissable_edge(v[1],v[2],v[0],v[3]))
      return FALSE;
    if (!admissable_edge(v[1],v[3],v[0],v[2]))
      return FALSE;
    if (!admissable_edge(v[2],v[3],v[0],v[1]))
      return FALSE;
   
	  
	 //what is admissable will have to change//
	//i.e. if the link of the vertex is now disconnected this is inadmissable//
	  //but if the link is connected but isn't necessarily a sphere it's admissable//
   // if (!admissable_vertex(v[0],v[1],v[2],v[3]))
     // return FALSE;
    //if (!admissable_vertex(v[1],v[0],v[2],v[3]))
     // return FALSE;
    //if (!admissable_vertex(v[2],v[0],v[1],v[3]))
     // return FALSE;
    //if (!admissable_vertex(v[3],v[0],v[1],v[2]))
      //return FALSE;
    
    /* add a new tetrahedron */
    
    add_tetrahedron_p(v,type);
	  
    /* check that (0,1) still has minimal degree of complete edges */
    
    for (i=0; i<4-1; i++)
      for (j=i+1; j<4; j++) {
	if (degree12_a[v[i]][v[j]] == degree13_a[v[i]][v[j]] &&
	    degree12_a[v[i]][v[j]] < degree12_a[0][1]) {
	  remove_tetrahedron_p(type);
	  return FALSE;
	}
      }
	  
	  
	//check that if a vertex became complete from this move then its link is connected//  
	for (i=0; i<4; i++) {
		if (complete_p[v[i]]) {
			if (!link_connected(v[i])) {
				remove_tetrahedron_p(type);
				return FALSE;
			}
		}
	}
	  
#if !defined NEIGHBORLY
    
    /* check for contractible edge */
    
    if (only_irreducible && nv_a > 5) 
      for (i=0; i<4; i++) {
	if (complete_a[v[i]])
	  for (vi=0; vi<nv_a; vi++) {
	    if (degree12_a[v[i]][vi] != 0) {
	      check_vi = TRUE;
	      for (j=0; check_vi && j<i; j++)
		check_vi = (vi != v[j]);
	      if (check_vi)
		if (complete_a[vi])
		  if (contractible(v[i],vi)) {
		    remove_tetrahedron_p(type);
		    return FALSE;
		  }
	    }
	  }
      }
    
#endif
    
    /* check if the just added tetrahedron forces additional tetrahedra to be
       added */
    //force_tetrahedron just always returns TRUE//
    if (!force_tetrahedron(v)) {
      remove_tetrahedron_p(type);
      return FALSE;
    }

    /* pruning after adding tetrahedron */
	  int temporaryThing = 0;
	  
	  if (v[0]==0 && v[1]==2 && v[2]==3 && v[3]==5) {
		  temporaryThing =1;
	  }
    if (type == PICKED)
      if (!min_lex()) {
			  remove_tetrahedron_p(type);
			  return FALSE;
      }
    
  }

  /* check triangulation is done */
    
  if (type == PICKED) {
    done = TRUE;
	for (vi=0; done && vi<nv_p; vi++){
		//if link_connected is working properly it will catch every link that has Euler Char =4//
		//previously we were checking here that the link of each vi is connected because before we were getting disjoint surfaces as links//
		//However, now this check is done above, immediately once the link becomes complete//
      done = (complete_p[vi] /*&& (degree01_p[vi] - degree02_p[vi] + degree03_p[vi]<3) && link_connected(vi)*/);
	}
	if (vi > prev_closed_link){
		ADDBIG(closed_link[vi],1);
	}
	prev_closed_link = vi;
  
		  
    if (done) {
		int other;
		int a;
		
		
	//  if (nv_p == maxnv) {
		if(nv_p==7){
			num7++;
			//printf("found a 7 vertex %d\n",num7);
		}
		if(nv_p==8){
			num8++;
			//printf("found a 8 vertex %d\n",num8);
		}
		if(nv_p==9){
			num9++;
			//printf("found a 9 vertex %d\n",num9);
		}
		if(nv_p==10){
			num10++;
		  //   printf("found a 10 vertex %d\n",num10);
		}
		//print the number found every 50000 10-vertex triangulations if you would like//
		//if (num10%50000==0) {
		//	printf("%d,%d,%d,%d\n",num7,num8,num9,num10);
		//}
		
		E2=0;
		E1=0;
		E0=0;
		E0_t=0;
		E0_k=0;
		E91_k=0;
		E91_t=0;
		E92_k=0;
		E92_t=0;
		E93_k=0;
		E93_t=0;
		
		int manifold = 1;
		int Euler = -999999;
		
		
		EulerChar =-99999;
		EulerChar = nv_p-ne_p+nf_p-nt_p;
		
		if (EulerChar>maxEuler) {
			maxEuler=EulerChar;
		}
		
		int homology=-99;
		for (vi=0; vi<nv_p; vi++){
			
			Euler = degree01_p[vi] - degree02_p[vi] + degree03_p[vi];
			if(Euler == 2){
				
			}
			else{
				manifold = 0;
			}
		
			if (Euler>2 && nv_p==maxnv) {
				printf("GOT surfaces with EulerChar>2");
				exit(1);
			}
			if (Euler==2 && nv_p==maxnv) {
				E2++;
				//if (homRank(vi)!=1) {
				//	printf("error: homology of a Sphere is: %d\n", homRank(vi));
				//	exit(1);
				//}
			}
			if (Euler==1 && nv_p==maxnv) {
				E1++;
				//homology=homRank(vi);
				//if (homology!=0) {
				//	printf("error: homology of projective plane is not zero\n");
				//	exit(1);
				//}
			}
			if (Euler==0 && nv_p==maxnv) {
				//E0++;
				homology=homRank(vi);
				//if (!(homology==1 || homology==0)) {
				//	printf("homology: %d\n",homology);
				//	printf("homology of torus or klein is not 1 or 0\n");
				//	exit(1);
				//}
				if (homology==0) {
					E0_k++;
				}
				else{
					E0_t++;
				}
			}
			
			if (Euler==-1 && nv_p==maxnv) {
				E91_k++;
			}
			//9 vertices is not enough for the orientable surface with Euler=-2//
			if (Euler==-2 && nv_p==maxnv) {
				E92_k++;
			}
			if (Euler==-3 && nv_p==maxnv) {
				E93_k++;
			}
			if (Euler<-3 && nv_p==maxnv) {
				printf("Euler Char less than -3\n");
				exit(0);
			}
			 
		}
		
		if (manifold) {
			mcount++;
			//printf("manifold\n");
			//printf("mcount: %d \n",mcount);
		}
		
		found_one();
		
      
      /*
	dump_it();
      */
      

      remove_tetrahedron_p(type);
      return TRUE;
    }
	
		/* do it again */
		
		next_tetrahedron();
		
		remove_tetrahedron_p(type);
	
  
  }

  return TRUE;
}

void next_tetrahedron()
{
  /* a tetrahedron has just been added.  
     find what the next tetrahedron might be. */
	
  int v[4];
  int v2lim,v3lim;

  if (nt_p == splitlevel) {
#ifdef SPLITTEST
    splitcases++;
    return;
#endif
    if (splitcount-- != 0) return;
    splitcount = mod - 1;
  }

  v[0] = list_p[nt_p-1][0];
  v[1] = list_p[nt_p-1][1];
  v[2] = list_p[nt_p-1][2];
  v[3] = list_p[nt_p-1][3]+1;

  	

  /* check if v[0] is complete */

  if (complete_p[v[0]]) {
	  while (complete_p[v[0]]){
		  v[0]++;
	  }
    v[1] = v[0]+1;
    v[2] = v[1]+1;
    v[3] = v[2]+1;
	
  }
	

  /* check if (v[0],v[1]) is complete */
  //keep this, since//
  //once an edge becomes complete its link can no longer be connected//
  //its link does have to be connected//
  
  if (degree12_p[v[0]][v[1]] == degree13_p[v[0]][v[1]] &&
      degree12_p[v[0]][v[1]] != 0) {
    while (degree12_p[v[0]][v[1]] == degree13_p[v[0]][v[1]] &&
		   degree12_p[v[0]][v[1]] != 0){
		
      v[1]++;
	}
    v[2] = v[1]+1;
    v[3] = v[2]+1;
	  
	 
  }

  /* while (v[0],v[1]) is not on boundry */
  
  while (degree12_p[v[0]][v[1]] == 0 || degree12_p[v[0]][v[1]] == degree13_p[v[0]][v[1]]) {
	  //printf("v[0]: %d, v[1]: %d, v[2]: %d, v[3]: %d \n",v[0],v[1],v[2],v[3]);

    if (degree12_p[v[0]][v[1]] == 0 && !complete_p[v[1]]) {
      
      /* first use of (v[0],v[1]) */
      
      v2lim = MIN(nv_p+1,maxnv-1);
      for (v[2]=v[1]+1; v[2]<v2lim; v[2]++)
		  if ((degree12_p[v[0]][v[2]] == 0 || degree12_p[v[0]][v[2]] != degree13_p[v[0]][v[2]]) && 
			  (degree12_p[v[1]][v[2]] == 0 || degree12_p[v[1]][v[2]] != degree13_p[v[1]][v[2]]) &&
			  (v[2] == nv_p || !complete_p[v[2]])) {
				v3lim = MIN(MAX(nv_p,v[2]+1)+1,maxnv);
				for (v[3]=v[2]+1; v[3]<v3lim; v[3]++)
					if ((degree12_p[v[0]][v[3]] == 0 || degree12_p[v[0]][v[3]] != degree13_p[v[0]][v[3]]) &&
						(degree12_p[v[1]][v[3]] == 0 || degree12_p[v[1]][v[3]] != degree13_p[v[1]][v[3]]) &&
						(degree12_p[v[2]][v[3]] == 0 || degree12_p[v[2]][v[3]] != degree13_p[v[2]][v[3]]) &&
						(base[v[1]][v[2]][v[3]]->other_p[1] == -1) && (base[v[0]][v[2]][v[3]]->other_p[1] == -1) && 
						(v[3] >= nv_p || !complete_p[v[3]]))
							do_tetrahedron(v,PICKED);
		  }
    }
	  
    v[1]++;
    v[2] = v[1]+1;
    v[3] = v[2]+1;
    }

  /* while (v[0],v[1],v[2]) is not on boundry */

  while (v[2] < maxnv-1 &&
	 (base[v[0]][v[1]][v[2]]->other_p[0] == -1 ||
	  base[v[0]][v[1]][v[2]]->other_p[1] != -1)) {
    if (base[v[0]][v[1]][v[2]]->other_p[0] == -1 && !complete_p[v[2]]) {
      
      /* first use of (v[0],v[1],v[2]) */

      v3lim = MIN(MAX(nv_p,v[2]+1)+1,maxnv);
      for (v[3]=v[2]+1; v[3]<v3lim; v[3]++)
	if ((base[v[0]][v[1]][v[3]]->other_p[1] == -1) &&
	    (base[v[0]][v[2]][v[3]]->other_p[1] == -1) &&
	    (base[v[1]][v[2]][v[3]]->other_p[1] == -1) &&
	    (v[3] == nv_p || !complete_p[v[3]]))
	  do_tetrahedron(v,PICKED);
    }
    v[2]++;
    v[3] = v[2]+1;
  }

  /* (v[0],v[1],v[2]) is on boundry.  must be used */
  
  v3lim = MIN(MAX(nv_p,v[2]+1)+1,maxnv);
  for (; v[3]<v3lim; v[3]++)
    if ((base[v[0]][v[1]][v[3]]->other_p[1] == -1) &&
	(base[v[0]][v[2]][v[3]]->other_p[1] == -1) &&
	(base[v[1]][v[2]][v[3]]->other_p[1] == -1) &&
	(v[3] == nv_p || !complete_p[v[3]]))
      do_tetrahedron(v,PICKED);

}
 
static void
initialize_splitting(int minlevel, int hint, int maxlevel)
  
/* Set splitlevel and splitcount.  */
{
  splitlevel = hint;
  if (splitlevel > maxlevel) splitlevel = maxlevel;
  
  if (splitlevel < minlevel && splitlevel > 0)
    {
      if (minlevel <= maxlevel) splitlevel = minlevel;
      else                      splitlevel = 0;
    }
  if (mod == 1) splitlevel = 0;
  splitcount = res;
}

static int 
getargvalue(char *arg)
  
/* Find integer value of arguement. 
   arg is a pointer to a command-line argument.
   The value of the arguement is the function return value.
   An absent value is equivalent to 0.
*/
{
  int j,ans,neg;
  
  ans = 0;
  if (arg[0] == '-') {
    neg = -1;
    j = 1;
  }
  else {
    neg = +1;
    j = 0;
  }
  
  for (; arg[j] >= '0' && arg[j] <= '9'; ++j)
    ans = ans * 10 + (arg[j] - '0');
  
  if (arg[j] != '\0')
    return -999999;
  else
    return neg*ans;
}

void summarize() 
{
  /* summarize results */

  int lnv;

	printf("mcount: %d\n", mcount);
	
  if (verbose) {
    if (!ISZEROBIG(ngen_all)) {
      PRINTBIG(stderr,ngen_all);
      fprintf(stderr," generated, total\n");
    }
    for (lnv=0; lnv<MAXN; lnv++)
      if (!ISZEROBIG(ngenerated[lnv])) {
		  PRINTBIG(stderr,ngenerated[lnv]);
		  fprintf(stderr," generated, %d vertices\n",lnv);
      }
    for (lnv=0; lnv<MAXN; lnv++)
      if (!ISZEROBIG(closed_link[lnv])) {
		  PRINTBIG(stderr,closed_link[lnv]);
		  fprintf(stderr," times %d vertex links closed\n",lnv);
      }
  }
	
  printf("max Euler: %d\n", maxEuler);
	
  fprintf(stderr,"maximum value nv obtained = %d\n",max_inter_nv);

  PRINTBIG(stderr,ncalls_min_lex);
  fprintf(stderr," calls to min_lex\n");
}
int
main(argc,argv)
int argc;
char *argv[];

{
  int iarg;
  int badargs,gdefined;
  char *arg;
  int hint;
  int degree0,min_degree0,max_degree0;
  int res_digits;

#if CPUTIME
  struct tms timestruct0,timestruct1;
  
  times(&timestruct0);
#endif
 
  gdefined = FALSE;
  only_irreducible = FALSE;
  maxnv = 0;
  res = 0;
  mod = 1;
  badargs = FALSE;

  for (iarg = 0; iarg < argc ; ++iarg) fprintf(stderr,"%s ",argv[iarg]);
  fprintf(stderr,"\n");

  iarg = 1;
  while (iarg < argc) {
    arg = argv[iarg];
    if (strcmp(arg,"-v") == 0) {
      verbose = TRUE;
      iarg++;
    }
    else if (strcmp(arg,"-h") == 0) {
      fprintf(stderr,"%s\n",HELPTEXT);
      exit(1);
    }
    else if (strcmp(arg,"-r") == 0) {
      iarg++;
      if (iarg >= argc) {
	fprintf(stderr,"res value required after -r switch\n");
	badargs = TRUE;
      }
      else {
	res = getargvalue(argv[iarg]);
	iarg++;
	if (res < 0) {
	  fprintf(stderr,"res (%d) must be non-negative.\n",res);
	  badargs = TRUE;
	  res = 0;
	}
      }
    }
    else if (strcmp(arg,"-m") == 0) {
      iarg++;
      if (iarg >= argc) {
	fprintf(stderr,"mod value required after -m switch\n");
	badargs = TRUE;
      }
      else {
	mod = getargvalue(argv[iarg]);
	iarg++;
	if (mod < 1) {
	  fprintf(stderr,"mod (%d) must be posotive.\n",mod);
	  badargs = TRUE;
	  mod = 1;
	}
      }
    }
    else if (strcmp(arg,"-i") == 0) {
      only_irreducible = TRUE;
      iarg++;
    }
    else {
      if (maxnv > 0) {
	fprintf(stderr,"redefining nv\n");
	badargs = TRUE;
      }
      else
	maxnv = getargvalue(arg);
      iarg++;
      if (maxnv == -999999) {
	fprintf(stderr,"unknown switch %s\n",arg);
	badargs = TRUE;
      }
      if (maxnv < 4) {
	fprintf(stderr,"nv (%d) too small.\n",maxnv);
	badargs = TRUE;
      }
    }
  }

  if (maxnv == 0) {
    fprintf(stderr,"nv not specified\n");
    badargs = TRUE;
  }

  if (maxnv > MAXN) {
    fprintf(stderr,"nv (%d) too large.  increase MAXN.\n",maxnv);
    badargs = TRUE;
  }

  if (res >= mod) {
    fprintf(stderr,"res (%d) >= mod (%d).\n",res,mod);
    badargs = TRUE;
    res = 0;
    mod = 1;
  }

  maxne = maxnv*(maxnv-1)/2;

  if (maxne > MAXE) {
    fprintf(stderr,
	    "maximum number of edges (%d) too large. increase MAXE.\n",
	    maxne);
    badargs = TRUE;
  }

  maxnf = maxnv*(maxnv-1)*(maxnv-2)/(3*2);

  if (maxnf > MAXF) {
    fprintf(stderr,
	    "maximum number of edges (%d) too large. increase MAXF.\n",
	    maxnf);
    badargs = TRUE;
  }

  maxnt = maxne - maxnv; //This is because of the Euler characteristic//
						 //Will be different for pseudomanifolds//

  if (maxnt > MAXT) {
    fprintf(stderr,
	    "maximum number of tetrahedra (%d) too large. increase MAXT.\n",
	    maxnt);
    badargs = TRUE;
  }

  if (badargs) {
    fprintf(stderr,"Usage: %s\n",USAGE);
    exit(1);
  }
  
#ifdef SPLITTEST
  if (mod == 1) mod = 2;
#endif

  if (verbose) {
    fprintf(stderr,"Version %s\n",VERSION);
    fprintf(stderr,"Number of vertices: %d\n", maxnv);
    fprintf(stderr,"Maximum number of tetrahedra: %d\n", maxnt);
    if (only_irreducible)
      fprintf(stderr,"Only irreducible triangulations are generated.\n");
    fprintf(stderr,"res/mod = %d/%d\n",res,mod);
  }

  hint = MIN(maxnt/2, 54);

  initialize_splitting(4,hint,maxnt-1);

  if (verbose && mod != 1)
    fprintf(stderr,"splitlevel is at %d tetrahedra.\n",splitlevel);

  sprintf(res_text,"%d",mod-1);
  res_digits = strlen(res_text);
  sprintf(res_text,"%c%d.%dd",'%',res_digits,res_digits);
  sprintf(res_text,res_text,res);

  initialize();

  min_degree0 = 3;
  max_degree0 = maxnv-2;
  if (only_irreducible)
    max_degree0 = MIN(maxnv-3,max_degree0);
	
  for (degree0=min_degree0; degree0 <= max_degree0; degree0++) {
    initialize_first_edge(degree0);
    
    next_tetrahedron();
  }

#if CPUTIME
  times(&timestruct1);
#endif
  
#ifdef SPLITTEST
  fprintf(stderr,"%d splitting cases at level = %d",splitcases,splitlevel);
#if CPUTIME
  fprintf(stderr,"; cpu=%.2f sec\n",
	  (double)(timestruct1.tms_utime+timestruct1.tms_stime
		   -timestruct0.tms_utime-timestruct0.tms_stime) / 
	  (double)CLK_TCK);
#else
  fprintf(stderr,"\n");
#endif
  return 0;
#endif
  
  summarize();
  
/*#if CPUTIME
  fprintf(stderr,"cpu=%.2f sec\n",
	  (double)(timestruct1.tms_utime+timestruct1.tms_stime
		   -timestruct0.tms_utime+timestruct0.tms_stime) / 
	  (double)CLK_TCK);
#else
  fprintf(stderr,"\n");
#endif*/

  exit(0);
}
