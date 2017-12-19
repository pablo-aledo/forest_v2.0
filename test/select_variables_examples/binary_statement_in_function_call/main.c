void __VERIFIER_assert(int val);

int fuubaa (int val_a, int val_b){
    return val_a^val_b;
}

int main () {
 int a = 1;
 int b = 1;
 int c = fuubaa (a, b);
 
__VERIFIER_assert(c == 1);

}
