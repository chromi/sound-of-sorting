// Routines to explore Frobenius theory.
// (c) 2021 Jonathan Morton <chromatix99@gmail.com>

#pragma once

// Input: a set of basis factors.
// A Frobenius tree is calculated from them to speed subsequent calculations.

// Outputs:
// Test whether any given integer can be obtained as a linear combination of the input factors.
// The GCD of the basis factors; no integer not a multiple of this GCD can be obtained.
// The reduced Frobenius number; the highest multiple of the GCD that cannot be obtained.
// Determine all multiples of an additional factor below some limit which cannot be obtained.

#include <algorithm>
#include <deque>
#include <vector>

#include <math.h>
#include <stdint.h>
#include <stdio.h>

#define unlikely(x)	__builtin_expect(!!(x), 0)

using std::sort;

using std::deque;
using std::vector;

// from sequences.cpp
extern uint64_t gcd(uint64_t, uint64_t);

class Frobenius
{
protected:
	vector<uint64_t> basis;
	vector<uint8_t>  tree;
	uint64_t         gcd;
	uint64_t         frobenius;

	static constexpr size_t maxSmartBasis = 1ULL << 32;

public:
	Frobenius(vector<uint64_t> factors, uint64_t limit = ~((uint64_t) 0)) :
		basis(factors),
		tree(),
		gcd(1),
		frobenius(~((uint64_t) 0))
	{
		// corner cases
		if(basis.size() == 1) {
			gcd = basis[0];
			frobenius = 0;	// any multiple of a single value can be obtained
		}
		if(basis.size() < 2)
			return;

		// Calculate the overall GCD
		gcd = basis[0];
		for(size_t i=1; i < basis.size(); i++)
			gcd = ::gcd(gcd, basis[i]);

		// Calculate the tree modulo the reduced smallest factor
		sort(basis.begin(), basis.end());
		const uint64_t a = basis[0] / gcd;

		// If we can't allocate enough memory to run the BFDU algorithm, we abort.
		// We also revert to the "dumb" algorithm if we're too close to the selected analysis limit.
		if(a != (size_t) a || a >= maxSmartBasis || a > pow(limit, 2/3.0))
			return;

		vector<uint64_t> S;	// path total weights
		vector<bool>   inQ;	// node is in queue?
		deque<size_t>    Q;	// processing queue

		try {
			tree.resize(a);
			S.resize(a);
			inQ.resize(a);
		} catch(std::bad_alloc& e) {
			tree.resize(0);
			tree.shrink_to_fit();
			return;
		}

		// Beihoffer-Nijenhuis BFDU algorithm
		tree[0] = basis.size() >= 255 ? 255 : basis.size()-1;
		S[0] = 0;
		inQ[0] = true;
		Q.push_back(0);

		for(size_t i=1; i < a; i++) {
			tree[i] = 0;
			S[i] = ~((uint64_t) 0);
			inQ[i] = false;
		}

		while(!Q.empty()) {
			const size_t v = Q.front();
			Q.pop_front();
			inQ[v] = false;

			// iterate over outgoing live paths from node v
			for(size_t j=1; j <= tree[v]; j++) {
				const size_t   u = (v + basis[j] / gcd) % a;
				const uint64_t w = S[v] + basis[j] / gcd;

				// check for overflow
				if(w < S[v] || w < basis[j] / gcd || w > limit)
					break;

				// update node u
				if(w < S[u]) {
					S[u] = w;
					tree[u] = j;

					if(!inQ[u]) {
						inQ[u] = true;
						Q.push_back(u);
					}
				}
			}
		}

		// Obtain the Frobenius number
		uint64_t mS = 0;
		for(size_t i=1; i < a; i++) {
			if(!tree[i]) {
				// node was not reached - Frobenius number is not representable, so leave it at maximum
				return;
			}

			if(mS < S[i])
				mS = S[i];
		}
		if(~((uint64_t) 0) / gcd > (mS - a))
			frobenius = gcd * (mS - a);

		// The Frobenius tree is now encoded in tree[] and can be used to identify whether (and how) an integer can be obtained from the basis.
		// NB: Any basis factors beyond the 256th rank will not be used.
		//     This is not a problem as long as they are above the actual Frobenius number, or linearly dependent themselves.
		//     One of these conditions is always true for all interesting Shellsort sequences.
	}

	uint64_t getGCD(void) const { return gcd; }
	uint64_t getFrobenius(void) const { return frobenius; }

	bool isObtainableBruteForce(uint64_t x) const {
		// easy cases
		if(basis.empty())
			return false;
		if(x % gcd)
			return false;
		if(x > frobenius)
			return true;
		if(x < basis[0])
			return false;

		vector<uint64_t> multiples(basis.size(), 0);
		uint64_t sum = 0;
		size_t i = basis.size();

		do {
			while(--i) {
				multiples[i] = (x - sum) / basis[i];
				sum += multiples[i] * basis[i];
			}

			if(!((x - sum) % basis[0]))
				return true;

			while(i < basis.size() && !multiples[i])
				i++;

			if(i < basis.size()) {
				multiples[i]--;
				sum -= basis[i];
			}
		} while(i < basis.size());

		return false;
	}

	void printObtainPathBruteForce(uint64_t x) const {
		if(basis.empty()) {
			fprintf(stderr, "No basis factors.\n");
			return;
		}

		fprintf(stderr, "%18lu: ", x);

		if(x % gcd) {
			fprintf(stderr, "is coprime to all the basis factors (GCD = %lu).\n", gcd);
			return;
		}

		vector<uint64_t> multiples(basis.size(), 0);
		uint64_t sum = 0;
		size_t i = basis.size();

		do {
			while(--i) {
				multiples[i] = (x - sum) / basis[i];
				sum += multiples[i] * basis[i];
			}

			if(!((x - sum) % basis[0])) {
				multiples[0] = (x - sum) / basis[0];
				sum = 0;

				bool firstFactor = true;
				for(size_t j = 0; j < basis.size(); j++) {
					if(multiples[j]) {
						fprintf(stderr, "%s%lu*%lu", firstFactor ? "" : " + ", multiples[j], basis[j]);
						firstFactor = false;
						sum += basis[j] * multiples[j];
					}
				}

				fprintf(stderr, " = %lu\n", sum);
				return;
			}

			while(i < basis.size() && !multiples[i])
				i++;

			if(i < basis.size()) {
				multiples[i]--;
				sum -= basis[i];
			}
		} while(i < basis.size());

		fprintf(stderr, "is not obtainable from the basis factors.\n");
	}

	bool isObtainable(uint64_t x) const {
		// if the tree couldn't be built due to lack of memory, brute-force it
		if(tree.empty())
			return isObtainableBruteForce(x);

		// easy cases
		if(x % gcd)
			return false;
		if(x > frobenius)
			return true;
		if(x < basis[0])
			return false;

		// use the tree
		const size_t a = tree.size();
		size_t   v = (x / gcd) % (basis[0] / gcd);
		uint64_t w = 0;

		while(v && w * gcd < x) {
			if(!tree[v]) {
				// this node was skipped due to overflow
				return false;
			}

			uint64_t d = basis[tree[v]] / gcd;
			v = (v + a - (d % a)) % a;
			w += d;
		}

		return w * gcd <= x;
	}

	void printObtainPath(uint64_t x) const {
		if(tree.empty()) {
			fprintf(stderr, "Path tree is empty.\n");
			return;
		}

		fprintf(stderr, "%18lu: ", x);

		if(x % gcd) {
			fprintf(stderr, "is coprime to all the basis factors (GCD = %lu).\n", gcd);
			return;
		}

	//	if(!isObtainable(x)) {
	//		fprintf(stderr, "is not obtainable from the basis factors.\n");
	//		return;
	//	}

		const size_t a = tree.size();
		size_t   v = (x / gcd) % (basis[0] / gcd);
		uint64_t w = 0;

		while(v && w * gcd < x) {
			if(!tree[v]) {
				fprintf(stderr, "was not reached in the path tree.\n");
				return;
			}

			fprintf(stderr, "%s%lu", w ? " + " : "", basis[tree[v]]);

			uint64_t d = basis[tree[v]] / gcd;
			v = (v + a - (d % a)) % a;
			w += d;
		}

		fprintf(stderr, " = %lu\n", w * gcd);
	}

	vector<uint64_t> frobeniusSet(uint64_t base, uint64_t limit) const {
		vector<uint64_t> out;

		for(uint64_t i=0; i < limit/base; i++) {
			uint64_t x = base * (i+1);

			if(x > frobenius)
				break;

			if(!isObtainable(x)) {
			//	if(!isObtainableBruteForce(x)) {
					out.push_back(x);
			//	} else {
			//		fprintf(stderr, "Mismatch between smart and brute-force results...\n");
			//		fprintf(stderr, "Smart: "); printObtainPath(x);
			//		fprintf(stderr, "Brute: "); printObtainPathBruteForce(x);
			//	}
			}
		}

		return out;
	}

	vector<uint64_t> frobeniusSetBruteForce(uint64_t base, uint64_t limit) const {
		vector<uint64_t> out;

		for(uint64_t i=0; i < limit/base; i++) {
			uint64_t x = base * (i+1);

			if(x > frobenius)
				break;

			if(!isObtainableBruteForce(x))
				out.push_back(x);
		}

		return out;
	}

	vector<uint64_t> redundantFactors(void) const {
		vector<uint64_t> out;
		vector<bool>     used(256, false);

		for(size_t i=1; i < tree.size(); i++)
			used[tree[i]] = true;

		for(size_t i=1; i < basis.size(); i++)
			if(!used[i])
				out.push_back(basis[i]);

		return out;
	}

	bool verify(void) const {
		vector<uint64_t> redundant = redundantFactors();
		bool prompted = false;

		// Forgive the Frobenius number being "infinity".
		if(!!(frobenius+1) && (isObtainable(frobenius) || !isObtainable(frobenius+1))) {
			fprintf(stderr, "Frobenius number obtained is incorrect.\n");
			return false;
		} else {
			fprintf(stderr, "Frobenius number:  %lu\n", frobenius);
		}

		if(redundant.empty())
			return true;

		for(size_t i=0; i < redundant.size(); i++) {
			if(isObtainable(redundant[i]))
				continue;
			if(!prompted)
				fprintf(stderr, "Unused factors needed:");
			prompted = true;
			fprintf(stderr, " %lu", redundant[i]);
		}

		if(prompted)
			fprintf(stderr, "\n");
		else
			fprintf(stderr, "All redundant factors accounted for.\n");

		return !prompted;
	}
};

