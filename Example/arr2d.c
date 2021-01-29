int arr[3][4];

int ith(int *ptr, int i, int n) {
	return ptr[i];
}

int main() {
	arr[1][2] = 5;
	return (ith((int*) arr, 6, 12));
}