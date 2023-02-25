void *calloc(int n, int size);
int printf(char *fmt, int val);

typedef struct node_t Node;
struct node_t {
    int val;
    Node *next;
};

void push_back(Node **cur, int val) {
    Node *new_node = calloc(1, sizeof(Node));
    new_node->val = val;
    (*cur)->next = new_node;
    *cur = new_node;
}

void print(Node *cur) {
    while (cur != 0) {
        printf("%d ", cur->val);
        cur = cur->next;
    }
    printf("\n");
}

int main() {
    Node head;
    Node *cur = &head;
    push_back(&cur, 1);
    push_back(&cur, 2);
    push_back(&cur, 3);
    print(head.next);
    return 0;
}
