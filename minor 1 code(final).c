#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <math.h>
#include <time.h>

// euclidean distance
#define d(a,b) (sqrt( ((a).x - (b).x)*((a).x - (b).x)\
			+ ((a).y - (b).y)*((a).y - (b).y)))

// swap two integer values
#define swap(x, y) if (&(x) != &(y)) {(x)^=(y); (y)^=(x) ; (x)^=(y); }

#define edge_swap(a, b) {_etmp = (a) ; (a) = (b); (b) = _etmp ; }

// a directed edge - used by mst algorithm
typedef struct {
  int i, j;
  double w;
} edge;

// a vertex
typedef struct {
  int degree;
  int *neighbours;
} vertex;

// a point in the plane
typedef struct {
  double x, y;
} point2d;

// approximation algorithms
enum { MST, CHRISTOFIDES };

// infinity
#ifndef INFINITY
#define INFINITY  HUGE_VAL
#endif // INFINITY

// two doubles that differ by at most EPSILON are considered equal
#define EPSILON 1.0e-6

// return the minimum of a and b
#ifndef min
#define min(a,b) ((a) < (b) ? (a) : (b))
#endif

// states of vertices in a tree traversal
enum { UNSEEN, VISITING, VISITED };

/* a qsort comparison function for edges - compares weights
 */
int cmp_edge_w(const void *a, const void *b)
{
  double w1, w2;

  w1 = ((edge*)a)->w;
  w2 = ((edge*)b)->w;
  if (w1 < w2) return -1;
  if (w1 == w2) return 0;
  return 1;
}

/* a qsort comparison function for edges - compares source vertices
 */
int cmp_edge_i(const void *a, const void *b)
{
  int i1, i2;

  i1 = ((edge*)a)->i;
  i2 = ((edge*)b)->i;
  return i1 - i2;
}


/* Convert the m edges in e into a set of n vertices
 */
void edges2vertices(edge *e, int m, vertex *v, int n)
{
  int i, j, l;

  // compute everyone's degree
  for (i = 0; i < n; i++) {
    v[i].degree = 0;
  }
  for (l = 0; l < m; l++) {
    v[e[l].i].degree++;
    v[e[l].j].degree++;
  }

  // allocate neighbour arrays
  for (i = 0; i < n; i++) {
    v[i].neighbours = malloc(sizeof(int)*v[i].degree);
  }

  // fill neighbour arrays
  for (i = 0; i < n; i++) {
    v[i].degree = 0;
  }
  for (l = 0; l < m; l++) {
    i = e[l].i;
    j = e[l].j;
    v[i].neighbours[v[i].degree++] = j;
    v[j].neighbours[v[j].degree++] = i;
  }
}

/* Determine if vertex i is reachable from vertex j in the graph gv
 */
int connected(vertex *gv, int n, int i, int j)
{
  int *seen, *fringe, f, k, t;

  seen = malloc(sizeof(int)*n);
  for (t = 0; t < n; t++)
    seen[t] = 0;
  fringe = malloc(sizeof(int)*n);
  f = 0;
  fringe[f++] = i;
  seen[i] = 1;
  while (f > 0) {
    i = fringe[--f];
    for (k = 0; k < gv[i].degree; k++) {
      if (gv[i].neighbours[k] == j) {
        free(fringe);
        free(seen);
        return 1;
      }
      if (!seen[gv[i].neighbours[k]]) {
        fringe[f++] = gv[i].neighbours[k];
        seen[gv[i].neighbours[k]] = 1;
      }
    }
  }
  free(fringe);
  free(seen);
  return 0;
}

/* Convert an Eulerian graph to an Euler tour.  This uses Fleury's Algorithm:
 * At each step we move across an edge e whose deletion does not disconnect g,
 * unless we have no choice.  Then we delete e.
 *
 * This is not as efficient as it could be.
 */
void euler_tour2(edge *g, int m, int n)
{
  int i, v, w, k, l, d, t;
  vertex *gv;

  // convert to adjacency list representation
  gv = malloc(sizeof(vertex)*n);
  edges2vertices(g, m, gv, n);

  v = 0;
  for (l = 0; l < m; l++) {
    g[l].i = v;
    d = gv[v].degree;
    assert(d > 0);
    gv[v].degree--;
    for (k = 0; k < d; k++) {
      // delete edge (v,w) from adjacency lists of v and w
      w = gv[v].neighbours[k];
      swap(gv[v].neighbours[k], gv[v].neighbours[gv[v].degree]);
      for (t = 0; gv[w].neighbours[t] != v; t++) assert(t < gv[w].degree);
      gv[w].degree--;
      swap(gv[w].neighbours[t], gv[w].neighbours[gv[w].degree]);
      if (d == 1 || connected(gv, n, v, w)) break;
      // reinsert (v,w)
      swap(gv[w].neighbours[t], gv[w].neighbours[gv[w].degree-1]);
      gv[w].degree++;
      swap(gv[v].neighbours[k], gv[v].neighbours[gv[v].degree]);
    }
    v = w;
    g[l].j = v;
  }
  // sanity check and cleanup
  for (i = 0; i < n; i++) {
    assert(gv[i].degree == 0);
    free(gv[i].neighbours);
  }
  for (l = 0; l < n; l++) {
    assert(g[l].j == g[(l+1)%m].i);
  }
  free(gv);
}

/*  Convert the Euler tour given by g to a tsp p by removing all but the
 *  first occurence of any vertex on the tour
 */
void euler2tsp(edge *g, int m, int *p, int n)
{
  int i, nout, l, *marked;

  marked = malloc(sizeof(int)*n);
  for (i = 0; i < n; i++) marked[i] = 0;
  nout = 0;
  for (l = 0; l < m; l++) {
    assert(g[l].j == g[(l+1)%m].i);
    if (!marked[g[l].i]) {
      marked[g[l].i] = 1;
      p[nout++] = g[l].i;
    }
  }
  assert(nout == n);
  free(marked);

}


/* Compute the minimum spanning tree of the cities using Prim's algorithm.
 * The tree is output as a sequence of n-1 edges.
 */
double mst(const point2d *cities, int n, edge *tree_edges)
{
  int i, j, k, l, m, e, cj, *comps;
  edge *edges;
  double wmst;

  // create an array of edges and sort by weight
  m = n*(n-1)/2;
  edges = malloc(sizeof(edge)*m);
  k = 0;
  for (i = 0; i < n-1; i++) {
    for (j = i+1; j < n; j++) {
      edges[k].i = i;
      edges[k].j = j;
      edges[k].w = d(cities[i], cities[j]);
      k++;
    }
  }
  assert(k == m);
  qsort(edges, m, sizeof(edge), cmp_edge_w);

  // construct the mst using Prim's Algorithm
  comps = malloc(sizeof(int)*n);	
  for (i = 0; i < n; i++)
    comps[i] = i;

  e = 0;
  wmst = 0;
  for (k = 0; k < m; k++) {
    i = edges[k].i;
    j = edges[k].j;
    if (comps[i] != comps[j]) {
      tree_edges[e++] = edges[k];
      wmst += edges[k].w;
      cj = comps[j];
      for (l = 0; l < n; l++) {
        if (comps[l] == cj) comps[l] = comps[i];
      }
    }
  }
  free(comps);
  free(edges);
  assert(e == n-1);
  return wmst;
}

/* Take the given spanning tree and make it Eulerian by finding a
 * minimum-weight perfect matching of its odd degree vertices.
 */
int make_eulerian(const point2d *cities, edge *tree_edges, int n)
{
  int i, j, l, *degrees, *odds, nodd;
  FILE *fp;
  char line[1000];

  // identify odd vertices
  degrees = malloc(sizeof(int)*n);
  for (i = 0; i < n; i++) degrees[i] = 0;
  for (l = 0; l < n-1; l++) {
    degrees[tree_edges[l].i]++;
    degrees[tree_edges[l].j]++;
  }
  nodd = 0;
  odds = malloc(sizeof(int)*n);
  for (i = 0; i < n; i++) {
    if (degrees[i] % 2 == 1) {
      odds[nodd++] = i;
    }
  }
  assert(nodd % 2 == 0);

  fp = fopen("min.txt", "w");
  assert(nodd >= 2);
  fprintf(fp, "%d %d\n", nodd, (nodd*(nodd-1))/2);
  for (l = 0; l < nodd; l++) {
    for (j = l+1; j < nodd; j++) {
      fprintf(fp, "%d %d %d\n", l, j,
             (int)(10e6*d(cities[odds[l]], cities[odds[j]])));
    }
  }
  fclose(fp);
  if (system("./blossom5 -V -e min.txt -w mout.txt") != 0) {
    fprintf(stderr, "\nError:No error\n");
    exit(-1);
  }

  // add matching edges to tree_edge array
  fp = fopen("mout.txt", "r");
  fgets(line, sizeof(line), fp);
  for (l = 0; l < nodd/2; l++) {
    assert(fgets(line, sizeof(line), fp) != NULL);
    assert(sscanf(line, "%d %d", &i, &j) == 2);
    tree_edges[l+n-1].i = odds[i];
    tree_edges[l+n-1].j = odds[j];
    tree_edges[l+n-1].w = d(cities[odds[i]], cities[odds[j]]);
  }
  fclose(fp);

  // quick sanity check
  for (i = 0; i < n; i++) degrees[i] = 0;
  for (l = 0; l < n - 1 + nodd/2; l++) {
    degrees[tree_edges[l].i]++;
    degrees[tree_edges[l].j]++;
  }
  for (i = 0; i < n; i++) {
    assert (degrees[i] % 2 == 0);
  }

  free(degrees);
  free(odds);
  return n - 1 + nodd/2;
}


/* Compute a 2-approximation to the TSP using the minimum spanning
 * tree heuristic.  This uses Kruskal's algorithm and runs in
 * O(n^2 log n) time.
 */
double tsp_mst(const point2d *cities, int n, int mode)
{
  int i, e, m, *p;
  edge *tree_edges;
  double wmst, wtsp;

  // compute the MST of the cities
  tree_edges = malloc(2*(n-1)*sizeof(edge));
  wmst = mst(cities, n, tree_edges);

  p = malloc(sizeof(int)*n);
  if (mode == MST) { // just compute 2-approximation using MST
    // double up tree edges and sort by source vertex
    for (e = 0; e < n-1; e++) {
      tree_edges[e+n-1] = tree_edges[e];
      swap(tree_edges[e+n-1].i, tree_edges[e+n-1].j);
    }
    m = 2*(n-1);
  } else if (mode == CHRISTOFIDES) {
    // use Christofides' heuristic
    m = make_eulerian(cities, tree_edges, n);
  }
  euler_tour2(tree_edges, m, n);
  euler2tsp(tree_edges, m, p, n);

  // compute tour length
  wtsp = d(cities[p[n-1]], cities[p[0]]);
  for (i = 0; i < n-1; i++) {
    wtsp += d(cities[p[i]], cities[p[i+1]]);
  }
  free(p);

  free(tree_edges);
  return wtsp;
}

/* Give a lower bound on the cost of extending the partial TSP given that
 * p[0],...,p[i] so that it includes p[i+1],...,p[n-1].
 * This lower bound uses the nearest neighbour heuristic :
 * each of p[i],...p[n-1] has a successor in the tsp. For p[j],
 * the distance to the successor can not be less than
 * min{d(p[j],p[k]) : k in {0,i,...j-1,j+1,...,n-1}}
 */
double tsp_bound(const point2d *cities,   // list of cities
                       int *p,            // permutation so far
                       int n,             // number of cities
                       int i)             // p[0],...,p[i-1] is fixed
{
  double b = 0, dmin;
  int j, k;

  for(j = i; j < n; j++) {
    dmin = d(cities[p[j]], cities[p[0]]);
    for(k = i; k < n; k++) {
      if (j != k) {
        dmin = min(dmin, d(cities[p[j]], cities[p[k]]));
      }
    }
    b += dmin;
  }
  return b;
}

/* The recursive helper for tsp_factorial (below)
 */
double tsp_factorial_r(const point2d *cities,   // list of cities
                       int *p,            // permutation so far
                       int n,             // number of cities
                       int i,             // p[0],...,p[i] is fixed
                       double w,          // weight of p[0],...,p[i-1]
	               int *popt,         // best solution so far
                       double *topt,      // cost of best solution so far
                       int bandb)         // to bound or not to bound
{
  int j;
  double t;

  // base case, we have a complete cycle
  if (i == n-1) {
    t = w + d(cities[p[0]], cities[p[n-1]]);
    if (t < *topt) {
      memcpy(popt, p, sizeof(int)*n);
      *topt = t;
    }
    return *topt;
  }

  if (bandb && w + tsp_bound(cities, p, n, i) >= *topt) {
      return *topt;
  }

  for (j = i+1; j < n; j++) {
    swap(p[i+1], p[j]);
    t = tsp_factorial_r(cities, p, n, i+1, w + d(cities[p[i]],cities[p[i+1]]),
                        popt, topt, bandb);
    swap(p[i+1], p[j]);
  }
  return *topt;
}

/* Uses a brute-force algorithm to compute an optimal travelling salesman
 * tour of the points in cities.  This run in O((n-1)!) time. If bandb = 1,
 * a bounding heuristic is used to speed this up.
 */
double tsp_factorial(const point2d *cities, int n, int bandb)
{
  int *p, *popt, i;
  double t, topt = INFINITY;

  p = malloc(sizeof(int)*n);
  for (i = 0; i < n; i++) {
    p[i] = i;
  }
  popt = malloc(sizeof(int)*n);
  tsp_factorial_r(cities, p, n, 0, 0.0, popt, &topt, bandb);

  /* do some error checking */
  t = d(cities[popt[n-1]], cities[popt[0]]);
  for (i = 1; i < n; i++) {
    t += d(cities[popt[i-1]], cities[popt[i]]);
  }
  assert(fabs(t - topt) <= EPSILON);
  free(p);
  free(popt);
  return topt;
}

/* Return a double approximation to n! (correct for non-negative n)
 */
double factorial(int n)
{
  int i;
  double fack = 1;

  for (i = 2; i < n; i++) {
    fack *= i;
  }
  return fack;
}
//tsp code
//
//
//
//
int ary[10][10],completed[10],n,cost=0;
//simple input of many localities with their respective Cost
void takeInput()
{
	int i,j;

	printf("Enter the number of Localities: ");
	scanf("%d",&n);

	printf("\nEnter the Cost Matrix\n");

	for(i=0;i < n;i++)
	{
		printf("\nEnter Elements of Row: %d\n",i+1);

		for( j=0;j < n;j++)
			scanf("%d",&ary[i][j]);

		completed[i]=0;
	}

	printf("\n\nThe cost list is:");

	for( i=0;i < n;i++)
	{
		printf("\n");

		for(j=0;j < n;j++)
			printf("\t%d",ary[i][j]);
	}
}
int least(int c)
{
	int i,nc=999;
	int min=999,kmin;

	for(i=0;i < n;i++)
	{
		if((ary[c][i]!=0)&&(completed[i]==0))
			if(ary[c][i]+ary[i][c] < min)
			{
				min=ary[i][0]+ary[c][i];
				kmin=ary[c][i];
				nc=i;
			}
	}

	if(min!=999)
		cost+=kmin;

	return nc;
}
void mincost(int city)
{
	int i,ncity;

	completed[city]=1;

	printf("%d--->",city+1);
	ncity=least(city);

	if(ncity==999)
	{
		ncity=0;
		printf("%d",ncity+1);
		cost+=ary[city][ncity];

		return;
	}

	mincost(ncity);
}


/* Run some tests of TSP algorithms
 */
 

int main(int argc, char *argv[])
{
  int y1;
  printf("Enter 1 for Travelling salesman :\nEnter 2 for Christofide:");
  scanf("%d", &y1);
  if(y1==2){
  int i, n = 0;
  point2d *cities;
  double topt;
  
  clock_t start, stop;

  if (argc == 1) {
    printf("Enter the number of localities:"); //take user input for cities
    scanf("%d",&n);
  } else {
    n = atoi(argv[1]);
  }
  if (n <= 0) {
    fprintf(stderr, "Usage: %s [n]\n", argv[1]);
  }

  printf("\n\nSolving the TSP for %d localities (number of tours ~ %.0lf)\n",
         n, factorial(n-1));
  // make a random point set
  cities = malloc(sizeof(point2d)*n);
  srand (time(0));
  for (i = 0; i < n; i++) {
    cities[i].x = rand();
    cities[i].y = rand();
  }

  printf("\n\nRunning MST TSP approximation");
  fflush(stdout);
  start = clock();
  topt = tsp_mst(cities, n, MST);
  stop = clock();
  printf("(%lf seconds)\n", (((double)stop)-start)/CLOCKS_PER_SEC);
  printf("Optimal tour length is at most %lf (MST)\n", topt);

  printf("\n\nRunning Christofides TSP approximation:");
  fflush(stdout);
  start = clock();
  topt = tsp_mst(cities, n, CHRISTOFIDES);
  stop = clock();
  printf(" (%lf seconds)\n", (((double)stop)-start)/CLOCKS_PER_SEC);
  printf("Optimal tour length is at most %lf (Christofides)\n", topt);

  printf("\n\nRunning B&B TSP...");
  fflush(stdout);
  start = clock();
  topt = tsp_factorial(cities, n, 1);
  stop = clock();
  printf("done (%lf seconds)\n", (((double)stop)-start)/CLOCKS_PER_SEC);
  printf("\nOptimal tour length is %lf\n", topt);

  printf("Running brute-force TSP...");
  fflush(stdout);
  start = clock();
  topt = tsp_factorial(cities, n, 0);
  stop = clock();
  printf("\ndone (%lf seconds)\n", (((double)stop)-start)/CLOCKS_PER_SEC);
  printf("\nOptimal tour length is %lf\n", topt);
  
  return 0;
}
else{
  takeInput();
  clock_t start, stop;
  printf("\n\nThe Path is:\n");
  mincost(0); //passing 0 because starting vertex

  printf("\n\nMinimum cost is %d\n ",cost);

  return 0;
}
}
