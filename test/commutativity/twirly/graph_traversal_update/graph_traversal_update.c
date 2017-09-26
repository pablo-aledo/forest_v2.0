const int MAX_N = 20;

struct vertex_t {
  int i;
};

struct graph_t {
  int n;
  struct vertex_t *vertices;
  int *adjacency[MAX_N];
};

struct graph_t graph_construct(void) {
  const int N = 5;
  static struct vertex_t vertices[N];

  vertices[0].i = 5;
  vertices[1].i = 15;
  vertices[2].i = 7;
  vertices[3].i = 3;
  vertices[4].i = 9;

  static int adjacency[][N] = {{1, 1, 1, 0, 1},
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
  int queue[MAX_N] = {0};
  int i = 0;
  int v = 0;
  int qelements = 0;
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

  return 0;
}
