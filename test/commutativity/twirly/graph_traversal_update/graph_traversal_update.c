
#include <stdio.h>
#include <stddef.h>

const size_t MAX_N = 20;

struct vertex_t {
  int i;
};

struct graph_t {
  size_t n;
  struct vertex_t *vertices;
  size_t *adjacency[MAX_N];
};

struct graph_t graph_construct(void) {
  const size_t N = 5;
  static struct vertex_t vertices[N];

  vertices[0].i = 5;
  vertices[1].i = 15;
  vertices[2].i = 7;
  vertices[3].i = 3;
  vertices[4].i = 9;

  static size_t adjacency[][N] = {{1, 1, 1, 0, 1},
                                  {1, 1, 0, 0, 1},
                                  {1, 0, 0, 1, 1},
                                  {0, 0, 1, 1, 0},
                                  {1, 1, 1, 0, 1}};

  static struct graph_t g;
  g.n = N;
  g.vertices = vertices;
  g.adjacency[0] = adjacency[0];
  g.adjacency[1] = adjacency[1];
  g.adjacency[2] = adjacency[2];
  g.adjacency[3] = adjacency[3];
  g.adjacency[4] = adjacency[4];

  return g;
}

int foo(struct vertex_t *v) { return v->i * v->i; }

int main(int argc, const char *argv[]) {
  struct graph_t g = graph_construct();
  char visited[MAX_N] = {0};
  size_t queue[MAX_N] = {0};
  size_t i = 0;
  size_t v = 0;
  size_t qelements = 0;
  int result = 0;

  queue[qelements++] = 3;

  while (qelements) {
    v = queue[--qelements];

    result += foo(&g.vertices[v]);

    for (i = 0; i < g.n; ++i) {
      if (g.adjacency[v][i]) {
        if (!visited[i]) {
          visited[i] = 1;
          queue[qelements++] = i;
        }
      }
    }
  }

  fprintf(stderr, "%d\n", result);
  fprintf(stderr, "%d\n", g.vertices[0].i);

  return 0;
}
