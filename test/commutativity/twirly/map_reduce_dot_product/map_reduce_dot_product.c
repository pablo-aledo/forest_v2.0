int main() {
  unsigned X[] = {14, 75, 66, 67, 64, 74, 44, 31};
  unsigned Y[] = {13, 41, 39, 12, 20, 70, 47};
  const int N = sizeof(X) / sizeof(unsigned);
  unsigned acc = 0;

  for (int i = 0; i < N; ++i)
    acc += X[i] + Y[i];

  return 0;
}
