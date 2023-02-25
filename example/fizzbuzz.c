int printf(char *fmt, int val);
int scanf(char *fmt, int *val);

int main() {
    int n;
    scanf("%d", &n);
    for(int i=1;i<=n;i++) {
        if (i % 15 == 0) {
            printf("FizzBuzz\n");
        } else if (i % 3 == 0) {
            printf("Fizz\n");
        } else if (i % 5 == 0) {
            printf("Buzz\n");
        } else {
            printf("%d\n", i);
        }
    }
}