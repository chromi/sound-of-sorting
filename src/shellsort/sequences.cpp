#include "sequences.hpp"

#include <algorithm>

#include <math.h>


// Sequences are generated up to 2^60, in ascending order.
// Only "systematic" sequences are considered.
static const uint64_t end = ((uint64_t) 1) << 60;

uint64_t gcd(uint64_t a, uint64_t b)
{
	while(b) {
		size_t c = a % b;
		a = b;
		b = c;
	}
	return a;
}

template<typename T>
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
	for(size_t k=0; k < 30; k++) {
		size_t g1 = 9 * ((1ULL << (2*k)) - (1ULL << k)) + 1;
		size_t g2 = 8 * (1ULL << (2*k+1)) - 6 * (1ULL << (k+1)) + 1;

		if(g1 < end) seq.seq.push_back(g1);
		if(g2 < end) seq.seq.push_back(g2);
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

static Sequence IncerpiBase(void) {
	const double base = 2.5;
	Sequence seq = { "IncerpiBase", "Base Factors for Incerpi-Sedgewick", {} };
	size_t i=1;

	while(true) {
		uint64_t x = ceil(pow(base, i++));
		if(x > end) break;

		while(!isFullyCoprime(seq.seq, x))
			x++;
		seq.seq.push_back(x);
	}

	seq.seq.insert(seq.seq.begin(), 1);
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

static Sequence CiuraLDE(void) {
	Sequence seq = { "CiuraLDE", "Ciura 2001 (continued with LDE optimisation)",
		// result of empirical search
		{ 1, 4, 10, 23, 57, 132, 301, 701, 1636, 3657, 8172, 18235, 40764, 91064, 203519, 454741,
			1016156, 2270499, 5073398, 11335582, 25328324, 56518561, 126451290, 282544198 }
	};

	// h[k+1] = 2.25 * h[k] + 1
	for(double gap=631315018; gap < end; gap = gap * 2.25 + 1)
		seq.seq.push_back((uint64_t) ceil(gap));

	return seq;
}

static Sequence Machoota(void) {
	Sequence seq = { "Machoota", "Machoota 2025",
		// result of empirical search
		{ 1, 4, 10, 23, 57, 132, 301, 701, 1504, 3263, 7196, 15948, 34644, 74428, 162005, 347077,
			745919, 1599893, 3446017, 7434649, 15933053 }
	};

	// extend with floor(2.22 * H_k-1)
	while(seq.seq.back() < end)
		seq.seq.push_back((uint64_t) floor(2.22 * seq.seq.back()));

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

static Sequence Leonardo2Plus(void) {
	Sequence seq = { "L2Plus", "Leonardo Squared plus 4 and 14", { 1, 4, 9, 14 } };
	Sequence pSeq = Leonardo2();

	for(size_t i=2; i < pSeq.seq.size(); i++)
		seq.seq.push_back(pSeq.seq[i]);

	return seq;
}

static Sequence Leonardo3(void) {
	Sequence seq = { "Leonardo3", "Leonardo Cubed", {} };

	for(uint64_t a=0, b=1, c=1; c*c*c < end; a=b, b=c, c += a+1)
		seq.seq.push_back(c*c*c);

	return seq;
}

static Sequence Leonardo3Plus(void) {
	Sequence seq = { "L3Plus", "Leonardo Squared plus 7 and 58", { 1, 7, 27, 58 } };
	Sequence pSeq = Leonardo3();

	for(size_t i=2; i < pSeq.seq.size(); i++)
		seq.seq.push_back(pSeq.seq[i]);

	return seq;
}

static void GeometricCoprime(Sequence& seq, const double base) {
	while(seq.seq.back() < end) {
		double x = seq.seq.back() * base;
		uint64_t i = ceil(x), j = floor(x);

		while(!isFullyCoprime(seq.seq, i))
			i++;
		while(!isFullyCoprime(seq.seq, j))
			j--;

		seq.seq.push_back((x-j) > (i-x) ? i : j);
	}
}

static Sequence RootFiveCoprime(void) {
	Sequence seq = { "Root5", "Root-5 Near-Geometric Coprime", { 1, 3 } };
	GeometricCoprime(seq, sqrt(5));
	return seq;
}

static Sequence LNBaseCoprime(void) {
	Sequence seq = { "LNBase", "e Near-Geometric Coprime", { 1, 4 } };
	GeometricCoprime(seq, exp(1));
	return seq;
}

static Sequence PiCoprime(void) {
	Sequence seq = { "Pi", "Pi Near-Geometric Coprime", { 1, 5 } };
	GeometricCoprime(seq, acos(-1));
	return seq;
}

static Sequence IncerpiLNBase(void) {
	std::vector<uint64_t> factors = LNBaseCoprime().seq;
	Sequence seq = { "IncerpiLNBase", "Incerpi-Sedgewick with e Near-Geometric Coprime factors", {} };

	factors.erase(factors.begin());

	// product of successive coprime factors, with one left out, triangular construction
	uint64_t z = 1;
	for(size_t i=0; i < 8; i++) {
		size_t x = factors[i];
		z *= x;

		// iterate down column, excluding one factor from the product at a time
		for(size_t j=i+1; j--;)
			seq.seq.push_back(z / factors[j]);
	}

	// product of the first 8 factors is near 2^56, good enough
	seq.seq.push_back(z);

	return seq;
}

static Sequence ConsecutiveFibonacci(void) {
	Sequence seq = { "Fib25", "Consecutive Fibonacci", {} };

	for(uint64_t a=0, b=1, c=1; b*c < end; a=b, b=c, c += a)
		seq.seq.push_back(b*c);

	return seq;
}

static Sequence ORLP(void) {
	Sequence seq = { "Orlp25", "Consecutive Orlp", { 1 } };

	for(uint64_t a=0, b=1, c=2; b*c < end; a=b, b=c, c = 2*a+1)
		seq.seq.push_back(b*c);

	return seq;
}

static Sequence ConvergentExponent(void) {
	Sequence seq = { "ConvExp", "Convergent Exponent", { 1 } };
	static const double e = exp(1), phi = (1+sqrt(5))/2;
	double harmonic = 0;

	while(seq.seq.back() < end) {
		double k = seq.seq.size();

		harmonic += 1/k;

		double x = pow(phi + e / harmonic, k);
		uint64_t i = ceil(x), j = floor(x);

		while(!isFullyCoprime(seq.seq, i))
			i++;
		while(!isFullyCoprime(seq.seq, j))
			j--;

		seq.seq.push_back((x-j) > (i-x) ? i : j);
	}

	return seq;
}

static Sequence ConvergentExponent2(void) {
	Sequence seq = { "ConvExp2", "Convergent Exponent 2", { 1 } };
	static const double phi = (1+sqrt(5))/2;
	double harmonic = 0;

	while(seq.seq.back() < end) {
		double k = seq.seq.size();

		harmonic += 1/k;

		double x = pow(phi + phi / harmonic, k);
		uint64_t i = ceil(x), j = floor(x);

		while(!isFullyCoprime(seq.seq, i))
			i++;
		while(!isFullyCoprime(seq.seq, j))
			j--;

		seq.seq.push_back((x-j) > (i-x) ? i : j);
	}

	return seq;
}

static Sequence ConvergentExponent3(void) {
	Sequence seq = { "ConvExp3", "Convergent Exponent 3", { 1 } };
	static const double phi = (1+sqrt(5))/2, r5 = sqrt(5);
	double harmonic = 0;

	while(seq.seq.back() < end) {
		double k = seq.seq.size();

		harmonic += 1/k;

		double x = pow(phi + r5 / harmonic, k);
		uint64_t i = ceil(x), j = floor(x);

		while(!isFullyCoprime(seq.seq, i))
			i++;
		while(!isFullyCoprime(seq.seq, j))
			j--;

		seq.seq.push_back((x-j) > (i-x) ? i : j);
	}

	return seq;
}

static void ExtendConvExp(Sequence& seq) {
	static const double e = exp(1), phi = (1+sqrt(5))/2;
	double harmonic = 0, k = 0, l = 1, b;

	if(seq.seq.empty())
		seq.seq.push_back(1);
	b = seq.seq.back();

	while(k < seq.seq.size())
		harmonic += 1.0 / ++k;

	while(seq.seq.back() < end) {
		double x = b * pow(phi + e / harmonic, l);
		uint64_t i = ceil(x), j = floor(x);

		while(!isFullyCoprime(seq.seq, i))
			i++;
		while(!isFullyCoprime(seq.seq, j))
			j--;

		seq.seq.push_back((x-j) > (i-x) ? i : j);

		harmonic += 1.0 / ++k;
		l++;
	}
}

static void ExtendConvExp2(Sequence& seq) {
	static const double phi = (1+sqrt(5))/2;
	double harmonic = 0, k = 0, l = 1, b;

	if(seq.seq.empty())
		seq.seq.push_back(1);
	b = seq.seq.back();

	while(k < seq.seq.size())
		harmonic += 1.0 / ++k;

	while(seq.seq.back() < end) {
		double x = b * pow(phi + phi / harmonic, l);
		uint64_t i = ceil(x), j = floor(x);

		while(!isFullyCoprime(seq.seq, i))
			i++;
		while(!isFullyCoprime(seq.seq, j))
			j--;

		seq.seq.push_back((x-j) > (i-x) ? i : j);

		harmonic += 1.0 / ++k;
		l++;
	}
}

static void ExtendConvExp3(Sequence& seq) {
	static const double phi = (1+sqrt(5))/2, r5 = sqrt(5);
	double harmonic = 0, k = 0, l = 1, b;

	if(seq.seq.empty())
		seq.seq.push_back(1);
	b = seq.seq.back();

	while(k < seq.seq.size())
		harmonic += 1.0 / ++k;

	while(seq.seq.back() < end) {
		double x = b * pow(phi + r5 / harmonic, l);
		uint64_t i = ceil(x), j = floor(x);

		while(!isFullyCoprime(seq.seq, i))
			i++;
		while(!isFullyCoprime(seq.seq, j))
			j--;

		seq.seq.push_back((x-j) > (i-x) ? i : j);

		harmonic += 1.0 / ++k;
		l++;
	}
}

static Sequence CiuraConvExp(void) {
	Sequence seq = { "CiuraConvExp", "Ciura 2001 (continued with Convergent Exponent)",
		// result of empirical search
		{ 1, 4, 10, 23, 57, 132, 301, 701 }
	};

	ExtendConvExp(seq);

	return seq;
}

static Sequence CiuraLDEConvExp(void) {
	Sequence seq = { "CiuraLDEConvExp", "Ciura 2001 (continued with LDE optimisation and ConvExp)",
		// result of empirical search
		{ 1, 4, 10, 23, 57, 132, 301, 701, 1636, 3657, 8172, 18235, 40764, 91064, 203519, 454741,
			1016156, 2270499, 5073398, 11335582, 25328324, 56518561, 126451290, 282544198, 631315018 }
	};

	ExtendConvExp(seq);

	return seq;
}

static Sequence MachootaConvExp(void) {
	Sequence seq = { "MachootaConvExp", "Machoota 2025 (continued with Convergent Exponent)",
		// result of empirical search
		{ 1, 4, 10, 23, 57, 132, 301, 701, 1504, 3263, 7196, 15948, 34644, 74428, 162005, 347077,
			745919, 1599893, 3446017, 7434649, 15933053 }
	};

	ExtendConvExp(seq);

	return seq;
}

static Sequence CiuraConvExp2(void) {
	Sequence seq = { "CiuraConvExp2", "Ciura 2001 (continued with Convergent Exponent 2)",
		// result of empirical search
		{ 1, 4, 10, 23, 57, 132, 301, 701 }
	};

	ExtendConvExp2(seq);

	return seq;
}

static Sequence CiuraLDEConvExp2(void) {
	Sequence seq = { "CiuraLDEConvExp2", "Ciura 2001 (continued with LDE optimisation and ConvExp2)",
		// result of empirical search
		{ 1, 4, 10, 23, 57, 132, 301, 701, 1636, 3657, 8172, 18235, 40764, 91064, 203519, 454741,
			1016156, 2270499, 5073398, 11335582, 25328324, 56518561, 126451290, 282544198, 631315018 }
	};

	ExtendConvExp2(seq);

	return seq;
}

static Sequence MachootaConvExp2(void) {
	Sequence seq = { "MachootaConvExp2", "Machoota 2025 (continued with Convergent Exponent 2)",
		// result of empirical search
		{ 1, 4, 10, 23, 57, 132, 301, 701, 1504, 3263, 7196, 15948, 34644, 74428, 162005, 347077,
			745919, 1599893, 3446017, 7434649, 15933053 }
	};

	ExtendConvExp2(seq);

	return seq;
}

static Sequence CiuraConvExp3(void) {
	Sequence seq = { "CiuraConvExp3", "Ciura 2001 (continued with Convergent Exponent 3)",
		// result of empirical search
		{ 1, 4, 10, 23, 57, 132, 301, 701 }
	};

	ExtendConvExp3(seq);

	return seq;
}

static Sequence CiuraLDEConvExp3(void) {
	Sequence seq = { "CiuraLDEConvExp3", "Ciura 2001 (continued with LDE optimisation and ConvExp3)",
		// result of empirical search
		{ 1, 4, 10, 23, 57, 132, 301, 701, 1636, 3657, 8172, 18235, 40764, 91064, 203519, 454741,
			1016156, 2270499, 5073398, 11335582, 25328324, 56518561, 126451290, 282544198, 631315018 }
	};

	ExtendConvExp3(seq);

	return seq;
}

static Sequence MachootaConvExp3(void) {
	Sequence seq = { "MachootaConvExp3", "Machoota 2025 (continued with Convergent Exponent 3)",
		// result of empirical search
		{ 1, 4, 10, 23, 57, 132, 301, 701, 1504, 3263, 7196, 15948, 34644, 74428, 162005, 347077,
			745919, 1599893, 3446017, 7434649, 15933053 }
	};

	ExtendConvExp3(seq);

	return seq;
}




std::vector<Sequence> sequences = {};

void populateSequences(void) {
	sequences.clear();

	sequences.push_back(Hibbard63());
	sequences.push_back(Pratt71(2,3));
	sequences.push_back(Pratt71(3,5));
	sequences.push_back(Pratt71(5,7));
	sequences.push_back(Pratt71(7,11));
	sequences.push_back(Knuth73());
	sequences.push_back(Sedgewick82(false));
	sequences.push_back(Sedgewick82(true));
	sequences.push_back(Sedgewick86());
	sequences.push_back(IncerpiSedgewick85());

	sequences.push_back(Tokuda92());
	sequences.push_back(CiuraTokuda());
	sequences.push_back(CiuraLDE());
	sequences.push_back(Machoota());

	sequences.push_back(Fibonacci());
	sequences.push_back(Fibonacci2());
	sequences.push_back(Fibonacci3());
	sequences.push_back(Leonardo());
	sequences.push_back(Leonardo2());
	sequences.push_back(Leonardo2Plus());
	sequences.push_back(Leonardo3());
	sequences.push_back(Leonardo3Plus());

	sequences.push_back(RootFiveCoprime());
	sequences.push_back(LNBaseCoprime());
	sequences.push_back(PiCoprime());

	sequences.push_back(ConvergentExponent());
	sequences.push_back(CiuraConvExp());
	sequences.push_back(CiuraLDEConvExp());
	sequences.push_back(MachootaConvExp());

	sequences.push_back(ConvergentExponent2());
	sequences.push_back(CiuraConvExp2());
	sequences.push_back(CiuraLDEConvExp2());
	sequences.push_back(MachootaConvExp2());

	sequences.push_back(ConvergentExponent3());
	sequences.push_back(CiuraConvExp3());
	sequences.push_back(CiuraLDEConvExp3());
	sequences.push_back(MachootaConvExp3());

	sequences.push_back(IncerpiBase());
	sequences.push_back(IncerpiLNBase());

	sequences.push_back(ConsecutiveFibonacci());
	sequences.push_back(ORLP());
}
