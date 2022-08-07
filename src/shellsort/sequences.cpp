#include "sequences.hpp"

#include <math.h>


// Sequences are generated up to 2^60, in ascending order.
// Only "systematic" sequences are considered.
static const uint64_t end = ((uint64_t) 1) << 60;

static uint64_t gcd(uint64_t a, uint64_t b)
{
	while(b) {
		size_t c = a % b;
		a = b;
		b = c;
	}
	return a;
}

template<T>
static bool isFullyCoprime(const std::vector<T>& ref, const T cand)
{
	for(size_t i=0; i < ref.size(); i++)
		if(gcd(ref[i], cand) != 1)
			return false;
	return true;
}



static Sequence Hibbard63(void) {
	Sequence seq = { "Hibbard", "Hibbard 1963", {} };

	// Mersenne numbers: (2^k - 1)
	for(uint64_t i=0, j=1; i < 60; i++, j |= j << 1)
		seq.seq.push_back(j);

	return seq;
}

static Sequence Pratt71(uint64_t a, uint64_t b) {
	Sequence seq = {
		"Pratt" + std::to_string(a) + std::to_string(b),
		"Pratt {" + std::to_string(a) + "," + std::to_string(b) + "} 1971",
		{}
	};

	// (a^p)(b^q) in sorted order
	for(uint64_t x=1; end / x >= a; x *= a)
		for(uint64_t y=x; end / y >= b; y *= b)
			seq.seq.push_back(y);
	std::sort(seq.seq.begin(), seq.seq.end());

	return seq;
}

static Sequence Knuth73(void) {
	Sequence seq = { "Knuth", "Knuth 1973", {} };

	// (3^k - 1) / 2, up to ceil(N/3)
	for(uint64_t p = 3; p / 2 < end / 3; p *= 3)
		seq.seq.push_back((p-1)/2);

	return seq;
}

static Sequence Sedgewick82(bool modified) {
	Sequence seq = {
		modified ? "Sedgewick82Mod" : "Sedgewick82",
		modified ? "Sedgewick 1982 Modified" : "Sedgewick 1982",
		{}
	};

	// original: 4^k + 3*2^(k-1) + 1, k >= 1, prefixed by 1
	// modified: floor(4^k) + floor(3*2^(k-1)) + 1, k >= -1
	seq.seq.push_back(1);
	if(modified)
		seq.seq.push_back(3);

	for(uint64_t a = 4, b = 3; a+b+1 < end; a <<= 2, b <<= 1)
		seq.seq.push_back(a+b+1);

	return seq;
}

static Sequence Sedgewick86(void) {
	Sequence seq = { "Sedgewick86", "Sedgewick 1986", {} };

	// even k: 9*(2^k - 2^(k/2)) + 1
	//  odd k: 8*2^k - 6*2^((k+1)/2) + 1
	for(uint64_t a=1, b=1; a*9 < end; a *= 2, b *= 2) {
		// even k
		seq.seq.push_back(9*(a-b) + 1);

		a *= 2;
		if(a*8 > end) break;

		// odd k
		seq.seq.push_back(8*a - 6*b + 1);
	}

	return seq;
}

static Sequence IncerpiSedgewick85(void) {
	const double base = 2.5;
	std::vector<size_t> factors;
	Sequence seq = { "Incerpi", "Incerpi-Sedgewick 1985", {} };

	// product of successive coprime factors, with one left out, triangular construction
	// start by obtaining the list of factors (first nine is enough for N <= 2^60)
	uint64_t z = 1;
	for(size_t i=1; i <= 9; i++) {
		size_t x = ceil(pow(base, i));
		while(!isFullyCoprime(factors, x))
			x++;
		factors.push_back(x);
		z *= x;

		// iterate down column, excluding one factor from the product at a time
		for(size_t j=i; j--;)
			seq.seq.push_back(z / factors[j]);
	}

	// product of the first 9 factors is pretty close to 2^60
	seq.seq.push_back(z);

	return seq;
}

static Sequence Tokuda92(void) {
	Sequence seq = { "Tokuda", "Tokuda 1992", {} };

	// h[k+1] = 2.25 * h[k] + 1
	for(double gap=1; gap < end; gap = gap * 2.25 + 1)
		seq.seq.push_back((uint64_t) ceil(gap));

	return seq;
}

static Sequence CiuraTokuda(void) {
	Sequence seq = { "Ciura", "Ciura 2001 (continued with Tokuda)",
		// result of empirical search
		{ 1, 4, 10, 23, 57, 132, 301 }
	};

	// h[k+1] = 2.25 * h[k] + 1
	for(double gap=701; gap < end; gap = gap * 2.25 + 1)
		seq.seq.push_back((uint64_t) ceil(gap));

	return seq;
}


// Above this comment are various well-established sequences.
// Below are some experimental unpublished sequences.

static Sequence Fibonacci(void) {
	Sequence seq = { "Fibonacci", "Fibonacci", {} };

	for(uint64_t a=0, b=1, c=1; c < end; a=b, b=c, c += a)
		seq.seq.push_back(c);

	return seq;
}

static Sequence Fibonacci2(void) {
	Sequence seq = { "Fibonacci2", "Fibonacci Squared", {} };

	for(uint64_t a=0, b=1, c=1; c*c < end; a=b, b=c, c += a)
		seq.seq.push_back(c*c);

	return seq;
}

static Sequence Fibonacci3(void) {
	Sequence seq = { "Fibonacci3", "Fibonacci Cubed", {} };

	for(uint64_t a=0, b=1, c=1; c*c*c < end; a=b, b=c, c += a)
		seq.seq.push_back(c*c*c);

	return seq;
}

static Sequence Leonardo(void) {
	Sequence seq = { "Leonardo", "Leonardo", {} };

	for(uint64_t a=0, b=1, c=1; c < end; a=b, b=c, c += a+1)
		seq.seq.push_back(c);

	return seq;
}

static Sequence Leonardo2(void) {
	Sequence seq = { "Leonardo2", "Leonardo Squared", {} };

	for(uint64_t a=0, b=1, c=1; c*c < end; a=b, b=c, c += a+1)
		seq.seq.push_back(c*c);

	return seq;
}

static Sequence Leonardo3(void) {
	Sequence seq = { "Leonardo3", "Leonardo Cubed", {} };

	for(uint64_t a=0, b=1, c=1; c*c*c < end; a=b, b=c, c += a+1)
		seq.seq.push_back(c*c*c);

	return seq;
}

static Sequence RootFiveCoprime(void) {
	Sequence seq = { "Root5", "Root-5 Near-Geometric Coprime", { 1, 5 } };
	const double root5 = sqrt(5);

	while(seq.seq.back() < end) {
		double x = seq.seq.back() * root5;
		uint64_t i = ceil(x), j = floor(x);

		while(!isFullyCoprime(seq.seq, i))
			i++;
		while(!isFullyCoprime(seq.seq, j))
			j--;

		seq.seq.push_back((x-j) > (i-x) ? i : j);
	}

	return seq;
}



std::vector<Sequence> sequences = {};

void populateSequences(void) {
	sequences.clear();

	sequences.push_back(Hibbard63());
	sequences.push_back(Pratt71(2,3));
	sequences.push_back(Pratt71(3,5));
	sequences.push_back(Pratt71(5,7));
	sequences.push_back(Knuth73());
	sequences.push_back(Sedgewick82(false));
	sequences.push_back(Sedgewick82(true));
	sequences.push_back(Sedgewick86());
	sequences.push_back(IncerpiSedgewick85());
	sequences.push_back(Tokuda92());
	sequences.push_back(CiuraTokuda());

	sequences.push_back(Fibonacci());
	sequences.push_back(Fibonacci2());
	sequences.push_back(Fibonacci3());
	sequences.push_back(Leonardo());
}
