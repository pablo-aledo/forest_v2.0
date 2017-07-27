struct whatever
{
 int a,b,c;
};

#define ALIGNMENT 4
#define ALIGN(X) (((X) + (ALIGNMENT - 1)) & (0 - ALIGNMENT))

int main() {

unsigned int size;
unsigned int pad;

// I don't know if this should be a passing case or not
// The value of pad is unknown, but the warning appears because
// sizeof(struct) + pad ==> [12,12] + [0,INF] == [0,INF]
// This design decision might be taken because + might overflow if pad is large
 return size / ALIGN(sizeof(struct whatever) + pad);
}
