#include <vector>
#include <stdint>
#include <stdlib>
#include <math>

template <T>
void tinyShellPass(std::vector<T>& A, const size_t gap)
{
	for(size_t i = gap; i < A.size(); i++)
		for(size_t j = i; j >= gap && A[j] < A[j-gap]; j -= gap)
			std::swap(A[j], A[j-gap]);
}

template <T>
void fastShellPass(std::vector<T>& A, const size_t gap)
{
	for(size_t i = gap; i < A.size(); i++) {
		const T tmp = A[i];
		for(size_t j = i; j >= gap; j -= gap) {
			if(tmp < A[j-gap]) {
				A[j] = A[j-gap];
			} else {
				if(j < i)
					A[j] = tmp;
				break;
			}
		}
	}
}

typedef struct {
	uint64_t	compares;	// compares can be expensive and may thus dominate runtime
	uint64_t	swaps;		// swaps or "exchanges" are the traditional measure of sorting cost
	uint64_t	writes;		// writes are a better measure for modern cached-memory architectures
	size_t		maxChain;	// to help validate estimates of worst-case performance
	size_t		gap;		// for per-pass telemetry
} Telemetry;

template <T>
void instrumentedShellPass(Telemetry& tm, std::vector<T>& A, const size_t gap)
{
	for(size_t i = gap; i < A.size(); i++) {
		uint64_t chain = 0;
		const T tmp = A[i];
		for(size_t j = i; j >= gap; j -= gap) {
			tm.compares++;
			if(tmp < A[j-gap]) {
				chain++;
				tm.swaps++;
				tm.writes++;
				A[j] = A[j-gap];
			} else {
				if(j < i) {
					tm.writes++;
					A[j] = tmp;
				}
				break;
			}
		}
		if(chain > tm.maxChain)
			tm.maxChain = chain;
	}
}

template <T>
std::vector<Telemetry> ShellSortHibbard63(std::vector<T>& A)
{
	std::vector<Telemetry> tmv;

	// (2^k - 1)
	size_t gap=A.size();
	for(int i=1; i < sizeof(gap)*8; i *= 2)
		gap |= gap >> i;

	while(gap >>= 1) {
		Telemetry tm = {0,0,0,0, gap};
		instrumentedShellPass(tm, A, gap);
		tmv.push_back(tm);
	}

	return tmv;
}

template <T>
void instrumentedCombPass(Telemetry& tm, std::vector<T>& A, const size_t gap)
{
	for(size_t i = gap; i < A.size(); i++) {
		tm.compares++;
		if(A[j] < A[j-gap]) {
			tm.swaps++;
			tm.writes += 2;
			std::swap(A[j]m A[j-gap]);
		}
	}
	if(tm.swaps && !tm.maxChain)
		tm.maxChain = 1;
}

template <T>
std::vector<Telemetry> ShellSortPratt71(std::vector<T>& A)
{
	std::vector<Telemetry> tmv;
	uint64_t p3[32] = {0};
	int      p2[32] = {0};

	// 3-smooth numbers: (2^p)(3^q) in sorted order
	for(uint64_t i=0, p=1; i < 32; i++, p *= 3) {
		p3[i] = p;
		while((p3[i] << p2[i]) < A.size())
			p2[i]++;
		for(size_t j=i; j > 0; j--) {
			if((p3[j] << p2[j]) < (p3[j-1] << p2[j-1])) {
				std::swap(p3[j], p3[j-1]);
				std::swap(p2[j], p2[j-1]);
			}
		}
	}

	int i = -1;
	while(i < 0 || p3[i] != 1 || p2[i] > 0) {
		if(--p2[++i] < 0) continue;
		size_t gap = p3[i] << p2[i];

		Telemetry tm = {0,0,0,0, gap};
		instrumentedCombPass(tm, A, gap);
		tmv.push_back(tm);
	}

	return tmv;
}

template <T>
std::vector<Telemetry> ShellSortKnuth73(std::vector<T>& A)
{
	std::vector<Telemetry> tmv;

	// (3^k - 1) / 2, up to ceil(N/3)
	uint64_t k=1, p=3;
	while(((p-1)/2)*3-2 < A.size()) {
		k++;
		p *= 3;
	}
	tmv.reserve(k);

	while(--k) {
		p /= 3;
		size_t gap = (p-1)/2;

		Telemetry tm = {0,0,0,0, gap};
		instrumentedShellPass(tm, A, gap);
		tmv.push_back(tm);
	}

	return tmv;
}

template <T>
std::vector<Telemetry> ShellSortSedgewick82(std::vector<T>& A)
{
	std::vector<Telemetry> tmv;

	// 4^k + 3*2^(k-1) + 1
	size_t k=31;
	static const uint64_t four = 4, three = 3;

	while(--k) {
		uint64_t gap = (four << (k*2)) + (three << k) + 1;
		if(gap > A.size()) continue;

		Telemetry tm = {0,0,0,0, gap};
		instrumentedShellPass(tm, A, gap);
		tmv.push_back(tm);
	}

	Telemetry tm = {0,0,0,0, 1};
	instrumentedShellPass(tm, A, 1);
	tmv.push_back(tm);

	return tmv;
}

template <T>
std::vector<Telemetry> ShellSortModifiedSedgewick82(std::vector<T>& A)
{
	std::vector<Telemetry> tmv;

	// floor(4^k) + floor(3*2^(k-1)) + 1
	uint64_t a = 0x4000000000000000, b = 0xC0000000;

	do {
		uint64_t gap = a + b + 1;
		a /= 4;
		b /= 2;
		if(gap > 1 && gap > A.size()) continue;

		Telemetry tm = {0,0,0,0, gap};
		instrumentedShellPass(tm, A, gap);
		tmv.push_back(tm);
	} while(a);

	return tmv;
}

template <T>
std::vector<Telemetry> ShellSortSedgewick86(std::vector<T>& A)
{
	std::vector<Telemetry> tmv;

	// even k: 9*(2^k - 2^(k/2)) + 1
	//  odd k: 8*2^k - 6*2^((k+1)/2) + 1
	uint64_t a = 0x800000000000000, b = 0x40000000;

	do {
		// odd k
		uint64_t gap = 8*a - 6*b + 1;
		if(gap < A.size()) {
			Telemetry tm = {0,0,0,0, gap};
			instrumentedShellPass(tm, A, gap);
			tmv.push_back(tm);
		}
		a /= 2;
		b /= 2;

		// even k
		gap = 9*(a-b) + 1;
		if(gap < A.size()) {
			Telemetry tm = {0,0,0,0, gap};
			instrumentedShellPass(tm, A, gap);
			tmv.push_back(tm);
		}
		a /= 2;
	} while(a);

	return tmv;
}

template <T>
std::vector<Telemetry> ShellSortTokuda92(std::vector<T>& A)
{
	std::vector<Telemetry> tmv;

	// h[k+1] = 2.25 * h[k] + 1
	std::vector<size_t> gaps;
	for(double gap=1; gap < A.size(); gap = gap * 2.25 + 1)
		gaps.push_back((size_t) ceil(gap));

	tmv.reserve(gaps.size());
	
	while(gaps.size()) {
		size_t gap = gaps.back();

		Telemetry tm = {0,0,0,0, gap};
		instrumentedShellPass(tm, A, gap);
		tmv.push_back(tm);

		gaps.pop_back();
	}

	return tmv;
}

template <T>
std::vector<Telemetry> ShellSortCiuraTokuda(std::vector<T>& A)
{
	std::vector<Telemetry> tmv;

	// Ciura's empirical sequence
	std::vector<size_t> gaps{ 1, 4, 10, 23, 57, 132, 301 };

	// h[k+1] = 2.25 * h[k] + 1
	for(double gap = 701; gap < A.size(); gap = gap * 2.25 + 1)
		gaps.push_back((size_t) ceil(gap));

	tmv.reserve(gaps.size());

	while(gaps.size()) {
		size_t gap = gaps.back();

		Telemetry tm = {0,0,0,0, gap};
		instrumentedShellPass(tm, A, gap);
		tmv.push_back(tm);

		gaps.pop_back();
	}

	return tmv;
}

template <T>
std::vector<Telemetry> ShellSortFibonacci(std::vector<T>& A)
{
	std::vector<Telemetry> tmv;

	// Fibonacci sequence
	size_t a=1, b=1, k=1;
	while(b < A.size()) {
		size_t c = a + b;
		a = b;
		b = c;
		k++;
	}
	tmv.reserve(k);

	while(b > 1) {
		size_t gap = a, c = b;
		b = a;
		a = c - b;

		Telemetry tm = {0,0,0,0, gap};
		instrumentedShellPass(tm, A, gap);
		tmv.push_back(tm);
	}

	return tmv;
}

template <T>
std::vector<Telemetry> ShellSortFibonacci2(std::vector<T>& A)
{
	std::vector<Telemetry> tmv;

	// Fibonacci sequence, squared
	size_t a=1, b=1, k=1;
	while(b*b < A.size()) {
		size_t c = a + b;
		a = b;
		b = c;
		k++;
	}
	tmv.reserve(k);

	while(b > 1) {
		size_t gap = a*a, c = b;
		b = a;
		a = c - b;

		Telemetry tm = {0,0,0,0, gap};
		instrumentedShellPass(tm, A, gap);
		tmv.push_back(tm);
	}

	return tmv;
}

template <T>
std::vector<Telemetry> ShellSortFibonacci3(std::vector<T>& A)
{
	std::vector<Telemetry> tmv;

	// Fibonacci sequence, cubed
	size_t a=1, b=1, k=1;
	while(b*b*b < A.size()) {
		size_t c = a + b;
		a = b;
		b = c;
		k++;
	}
	tmv.reserve(k);

	while(b > 1) {
		size_t gap = a*a*a, c = b;
		b = a;
		a = c - b;

		Telemetry tm = {0,0,0,0, gap};
		instrumentedShellPass(tm, A, gap);
		tmv.push_back(tm);
	}

	return tmv;
}

size_t gcd(size_t a, size_t b)
{
	while(b) {
		size_t c = a % b;
		a = b;
		b = c;
	}
	return a;
}

bool isFullyCoprime(const std::vector<size_t>& ref, const size_t cand)
{
	for(size_t i=0; i < ref.size(); i++)
		if(gcd(ref[i], cand) != 1)
			return false;
	return true;
}

template <T>
std::vector<Telemetry> ShellSortRootFiveCoprime(std::vector<T>& A)
{
	std::vector<Telemetry> tmv;

	// h[k+1] = nearest coprime to sqrt(5) * h[k]
	const double root5 = sqrt(5);
	std::vector<size_t> gaps{1, 5};

	while(gaps.back() < A.size()) {
		double x = gaps.back() * root5;
		size_t i = ceil(x);
		size_t j = floor(x);

		while(!isFullyCoprime(gaps, i))
			i++;
		while(!isFullyCoprime(gaps, j))
			j--;

		gaps.push_back((x-j) > (i-x) ? i : j);
	}

	tmv.reserve(gaps.size());
	
	while(gaps.size()) {
		size_t gap = gaps.back();

		Telemetry tm = {0,0,0,0, gap};
		instrumentedShellPass(tm, A, gap);
		tmv.push_back(tm);

		gaps.pop_back();
	}

	return tmv;
}

template <T>
std::vector<Telemetry> ShellSortIncerpiSedgewick(std::vector<T>& A)
{
	std::vector<Telemetry> tmv;

	// product of successive coprime factors, with one left out, triangular construction
	// start by obtaining the list of factors (first nine is enough for N <= 2^60)
	const double base = 2.5;
	std::vector<size_t> factors;

	for(size_t i=1; i <= 9; i++) {
		size_t x = ceil(pow(base, i));
		while(!isFullyCoprime(factors, x))
			x++;
		factors.push_back(x);
	}

	// find the column of the triangle covering the problem size
	size_t i;
	uint64_t product = 1;
	for(i=0; i < factors.size() && product < A.size(); i++)
		product *= factors[i];
	tmv.reserve(((i+1) * (i+2)) / 2);

	// iterate down each column in turn, excluding one factor from the product at a time
	do {
		for(size_t j=0; j <= i; j++) {
			uint64_t gap = product / factors[j];
			if(gap >= A.size()) continue;

			Telemetry tm = {0,0,0,0, gap};
			instrumentedShellPass(tm, A, gap);
			tmv.push_back(tm);
		}

		// next column
		product /= factors[i];
	} while(i--);

	return tmv;
}
