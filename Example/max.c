#define MAX(a,b) ((a < b) ? b : a)

int max3(int a, int b, int c) {
	int d = MAX(a,b);
	return MAX(d, c);
}

int min(int a, int b) {
	if (a == MAX(a,b)) {
		return b;
	}
	else {
		return a;
	}
}

int main() {
	return max3(3, 5, 1);
}