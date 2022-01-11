#define N 100
void vector_add(uint32_t* a, uint32_t* b, uint32_t* c) {
  int vec_len = a[N - 1];
  for (int i = 1; i < vec_len; i++)
    c[i] = a[i] + b[i] ;
}
void vector_add_wrapper(uint32_t *a, uint32_t* b, uint32_t* c) {

    public_in(__SMACK_value(a));
    public_in(__SMACK_value(a[N - 1]));
    public_in(__SMACK_value(b));
    public_in(__SMACK_value(c));

    vector_add(a, b, c);
}