int main() {
  unsigned int X[] = {14, 75, 66, 67, 64, 74, 44, 31};
  unsigned int Y[] = {13, 41, 39, 12, 20, 70, 47};
  unsigned int a = 19;
  const int N = sizeof(X) / sizeof(unsigned int);

  for (int i = 0; i < N; ++i)
    Y[i] = a * X[i] + Y[i];

  return 0;
}
