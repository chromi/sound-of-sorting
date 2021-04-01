/******************************************************************************
 * src/algorithms/insertion.cpp
 *
 * Implementations of insertion-based sorting algorithms.
 *
 * Note that these implementations may not be as good/fast as possible. Some
 * are modified so that the visualization is more instructive.
 *
 * Futhermore, some algorithms are annotated using the mark() and watch()
 * functions from SortArray. These functions add colors to the illustratation
 * and thereby makes the algorithm's visualization easier to explain.
 *
 ******************************************************************************
 * Copyright (C) 2013-2014 Timo Bingmann <tb@panthema.net>
 * Copyright (C) 2021 Jonathan Morton <chromatix99@gmail.com>
 *
 * This program is free software: you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the Free
 * Software Foundation, either version 3 of the License, or (at your option)
 * any later version.
 *
 * This program is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
 * more details.
 *
 * You should have received a copy of the GNU General Public License along with
 * this program.  If not, see <http://www.gnu.org/licenses/>.
 *****************************************************************************/

#include "SortAlgo.h"
#include "algorithms/insertion.h"

// ****************************************************************************
// *** Insertion Sort

// swaps every time (keeps all values visible)
void InsertionSort(SortArray& A)
{
	for (size_t i = 1; i < A.size(); ++i)
	{
		value_type key = A[i];
		A.mark(i);

		ssize_t j = i - 1;
		while (j >= 0 && A[j] > key)
		{
			A.swap(j, j+1);
			j--;
		}

		A.unmark(i);
	}
}

// with extra item on stack
void InsertionSort2(SortArray& A)
{
	for (size_t i = 1; i < A.size(); ++i)
	{
		value_type tmp, key = A[i];
		A.mark(i);

		ssize_t j = i - 1;
		while (j >= 0 && (tmp = A[j]) > key)
		{
			A.set(j + 1, tmp);
			j--;
		}
		A.set(j + 1, key);

		A.unmark(i);
	}
}

void BinaryInsertionSort(SortArray& A)
{
	for (size_t i = 1; i < A.size(); ++i)
	{
		value_type key = A[i];

		if(key >= A[i-1]) continue;

		A.mark(i);

		size_t lo = 0, hi = i;
		while (lo < hi) {
			size_t mid = (lo + hi) / 2;
			if (key < A[mid])
				hi = mid;
			else
				lo = mid + 1;
		}

		// item has to go into position lo
		A.unmark(i);
		A.rotate(lo, i, i+1);
	}
}

// ****************************************************************************
// *** Bubble Sort

void BubbleSort(SortArray& A)
{
	for (size_t i = 0; i < A.size()-1; ++i)
	{
		for (size_t j = 0; j < A.size()-1 - i; ++j)
		{
			if (A[j] > A[j + 1])
			{
				A.swap(j, j+1);
			}
		}
	}
}

// ****************************************************************************
// *** Cocktail Shaker Sort

// from http://de.wikibooks.org/wiki/Algorithmen_und_Datenstrukturen_in_C/_Shakersort

void CocktailShakerSort(SortArray& A)
{
	size_t lo = 0, hi = A.size()-1, mov = lo;

	while (lo < hi)
	{
		for (size_t i = hi; i > lo; --i)
		{
			if (A[i-1] > A[i])
			{
				A.swap(i-1, i);
				mov = i;
			}
		}

		lo = mov;

		for (size_t i = lo; i < hi; ++i)
		{
			if (A[i] > A[i+1])
			{
				A.swap(i, i+1);
				mov = i;
			}
		}

		hi = mov;
	}
}

// ****************************************************************************
// *** Gnome Sort

// from http://en.wikipediA.org/wiki/Gnome_sort

void GnomeSort(SortArray& A)
{
	for (size_t i = 1; i < A.size(); )
	{
		if (A[i] >= A[i-1])
		{
			++i;
		}
		else
		{
			A.swap(i, i-1);
			if (i > 1) --i;
		}
	}
}

// ****************************************************************************
// *** Shell Sort

// Shellsort is a very simple algorithm, whose performance depends heavily on the
// sequence of increments chosen.  More passes give less movement needed in each
// pass, but increase the minimum cost of the sort.  It is also important to make
// increments mutually co-prime, or nearly so.

// For illustrative purposes, a large number of such sequences have been provided
// here.  The default matches the sequence given in earlier versions, but this is
// not the best one known for average-case performance.

ShellSortIncrementType g_shellsort_increment = SHELL_1986_SEDGEWICK;

std::vector<size_t> ShellSortIncrements(size_t n, ShellSortIncrementType t)
{
	std::vector<size_t> incs;
	bool reverse = false;

	switch(t) {
		case SHELL_1959_SHELL: {
		// worst-case O(n^2)
		// N/2, N/4, ..., 1
			reverse = true;
			while(n /= 2)
				incs.push_back(n);
			break;
		}

		case SHELL_1960_FRANK: {
		// worst-case O(n^(3/2))
		// 2*floor(N/(2^k+1))+1
			reverse = true;
			n /= 2;
			do {
				n /= 2;
				incs.push_back(n*2+1);
			} while(n);
			break;
		}

		case SHELL_1963_HIBBARD: {
		// worst-case O(n^(3/2))
		// 2^k - 1
		// 1, 3, 7, 15, 31, 63, ...
			for(size_t j=1; j < n; j = j*2+1) {
				incs.push_back(j);
			}
			break;
		}

		case SHELL_1965_PAPERNOV: {
		// worst-case O(n^(3/2))
		// 2^k + 1
		// 1, 3, 5, 9, 17, 33, 65, ...
			incs.push_back(1);
			for(size_t j=2; j <= n; j *= 2) {
				incs.push_back(j+1);
			}
			break;
		}

		case SHELL_1971_PRATT: {
		// worst-case O(n (log n)^2), but high cost
		// (2^p)*(3^q) for all non-negative p and q, in order
		// 1, 2, 3, 4, 6, 8, 9, 12, ...
			for(size_t i=1; i < n; i *= 2) {
				for(size_t j=1; i*j < n; j *= 3) {
					size_t k = i*j;
					auto x = incs.begin();

					while(x != incs.end() && *x < k)
						x++;
					incs.insert(x, k);
				}
			}
			break;
		}

		case SHELL_1973_KNUTH: {
		// worst-case O(n^(3/2))
		// (3^k - 1) / 2, up to ceil(N/3)
		// 1, 4, 13, 40, 121, ...
			for(size_t i=3; i-1 <= n*2; i *= 3) {
				size_t j = (i-1) / 2;
				if(j*3 > n)
					break;
				incs.push_back(j);
			}
			break;
		}

		case SHELL_1982_SEDGEWICK: {
		// worst-case O(n^(4/3))
		// 4^k + 3*2^(k-1) + 1
		// 1, 8, 23, 77, 281, ...
			incs.push_back(1);
			for(size_t i=4, j=3; i+j+1 < n; i *= 4, j *= 2) {
				incs.push_back(i+j+1);
			}
			break;
		}

		case SHELL_1985_INCERPI: {
		// This is the moderately famous Incerpi-Sedgewick sequence.
		// generation function very complex, so taken by rote from OEIS A036569.
			incs.push_back(1);
			incs.push_back(3);
			incs.push_back(7);
			incs.push_back(21);
			incs.push_back(48);
			incs.push_back(112);
			incs.push_back(336);
			incs.push_back(861);
			incs.push_back(1968);
			incs.push_back(4592);
			incs.push_back(13776);
			incs.push_back(33936);
			incs.push_back(86961);
			incs.push_back(198768);
			incs.push_back(463792);
			incs.push_back(1391376);
			incs.push_back(3402672);
			incs.push_back(8382192);
			incs.push_back(21479367);
			incs.push_back(49095696);
			incs.push_back(114556624);
			incs.push_back(343669872);
			incs.push_back(852913488);
			incs.push_back(2085837936);

			while(incs.back() > n)
				incs.pop_back();
			break;
		}

		case SHELL_1986_SEDGEWICK: {
		// worst-case O(n^(4/3))
		// even k: 9*(2^k - 2^(k/2)) + 1
		//  odd k: 8*2^k - 6*2^((k+1)/2) + 1
		// 1, 5, 19, 41, 109, ...
			size_t i=1, j=1;
			while(true) {
				size_t k = 9*(i-j)+1;
				if(k > n) break;
				incs.push_back(k);

				i *= 2;
				j *= 2;

				k = 8*i - 6*j + 1;
				if(k > n) break;
				incs.push_back(k);

				i *= 2;
			}
			break;
		}

		case SHELL_1991_GONNET: {
		// worst-case complexity unknown; designed for average-case performance
		// H(0) = N; H(k) = floor(H(k-1) * 5/11)
			reverse = true;
			for(size_t h = n; h > 1; h = (h*5ULL)/11) {
				incs.push_back(h);
			}
			incs.push_back(1);
			break;
		}

		case SHELL_1992_TOKUDA: {
		// worst-case complexity unknown; designed for average-case performance
			for(double x=1; x < n; x = x * 2.25 + 1)
				incs.push_back((size_t) ceil(x));
			break;
		}

		case SHELL_2001_CIURA:
		case SHELL_CIURA_TOKUDA:
		case SHELL_CIURA_FIBONACCI:
		case SHELL_CIURA_FIBONACCI2:
		case SHELL_CIURA_FIBONACCI3:
		case SHELL_CIURA_ROOT5:
		case SHELL_CIURA_PRATT: {
		// worst-case complexity unknown; designed for average-case performance
		// not generated by a formula, but through empirical testing
			incs.push_back(1);
			incs.push_back(4);
			incs.push_back(10);
			incs.push_back(23);
			incs.push_back(57);
			incs.push_back(132);
			incs.push_back(301);
			incs.push_back(701);

			if(t == SHELL_CIURA_TOKUDA) {
				// extend sequence using Tokuda's formula, if needed; first is 1579
				for(double x = incs.back() * 2.25 + 1; x < n; x = x * 2.25 + 1)
					incs.push_back((size_t) ceil(x));
			} else if(t == SHELL_CIURA_PRATT) {
				// extend sequence using a Pratt recurrence, if needed;
				// (23^p)*(57^q) for all non-negative p and q, in order
				// asymptotic complexity becomes O(N log^2 N)
				for(size_t i=1; i < n; i *= 23) {
					for(size_t j=1; j < n; j *= 57) {
						size_t k = i*j;
						auto x = incs.begin();

						if(k >= n) break;
						if(k <= 701) continue;
						while(x != incs.end() && *x < k)
							x++;
						incs.insert(x, k);
					}
				}
			} else if(t == SHELL_CIURA_FIBONACCI) {
				size_t a = 301, b = 701, c = a+b;
				while(c < n) {
					incs.push_back(c);
					a = b;
					b = c;
					c = a+b;
				}
			} else if(t == SHELL_CIURA_FIBONACCI2) {
				size_t a = nearbyint(sqrt(301)), b = nearbyint(sqrt(701)), c = a+b;
				while(c < n) {
					incs.push_back(c*c);
					a = b;
					b = c;
					c = a+b;
				}
			} else if(t == SHELL_CIURA_FIBONACCI3) {
				size_t a = nearbyint(cbrt(301)), b = nearbyint(cbrt(701)), c = a+b;
				while(c < n) {
					incs.push_back(c*c*c);
					a = b;
					b = c;
					c = a+b;
				}
			} else if(t == SHELL_CIURA_ROOT5) {
				const double root5 = sqrt(5);
				size_t i = 701, j = 701;

				while(i < n) {
					double x = i * root5;
					i = floor(x);
					j = ceil(x);

					bool coprime;
					do {
						coprime = true;
						for(auto z = incs.begin(); z != incs.end(); z++) {
							size_t c = i, d = *z;
							while(d) {
								size_t e = c % d;
								c = d;
								d = e;
							}
							if(c > 1) {
								i--;
								coprime = false;
							}
						}
					} while(!coprime);

					do {
						coprime = true;
						for(auto z = incs.begin(); z != incs.end(); z++) {
							size_t c = j, d = *z;
							while(d) {
								size_t e = c % d;
								c = d;
								d = e;
							}
							if(c > 1) {
								j++;
								coprime = false;
							}
						}
					} while(!coprime);

					// pick coprime candidate closest to exact ratio
					if(x-i > j-x)
						i = j;

					incs.push_back(i);
				}
			}

			while(incs.back() > n)
				incs.pop_back();
			break;
		}

		case SHELL_FIBONACCI: {
		// consecutive Fibonacci numbers are coprime, which is good;
		// but ratio is about 1.6, which is less than empirical ideal.
		// 1, 2, 3, 5, 8, 13, 21, 34, ...
			size_t i=0, j=1, k=1;
			while(k < n) {
				incs.push_back(k);
				i = j;
				j = k;
				k = i+j;
			}
			break;
		}

		case SHELL_FIBONACCI_SQUARED: {
		// consecutive Fibonacci numbers are coprime, and so are their squares
		// ratio is about 2.6, which is in the empirically favourable range.
			size_t i=0, j=1, k=1;
			while(k*k < n) {
				incs.push_back(k*k);
				i = j;
				j = k;
				k = i+j;
			}
			break;
		}

		case SHELL_FIBONACCI_CUBED: {
		// consecutive Fibonacci numbers are coprime, and so are their cubes
		// but ratio is about 4.236, which is more than the empirical ideal.
			size_t i=0, j=1, k=1;
			while(k*k*k < n) {
				incs.push_back(k*k*k);
				i = j;
				j = k;
				k = i+j;
			}
			break;
		}

		case SHELL_ROOT5_COPRIME: {
		// Increment ratios of about 2.2 to 2.25 seem to work well,
		// sqrt(5) is about 2.236 which seems like an awfully nice coincidence.
		// Ensure all increments are mutually coprime using gcd.
			const double root5 = sqrt(5);
			size_t i = 5, j = 5;

			incs.push_back(1);

			while(i < n) {
				incs.push_back(i);

				double x = i * root5;
				i = floor(x);
				j = ceil(x);

				bool coprime;
				do {
					coprime = true;
					for(auto z = incs.begin(); z != incs.end(); z++) {
						size_t c = i, d = *z;
						while(d) {
							size_t e = c % d;
							c = d;
							d = e;
						}
						if(c > 1) {
							i--;
							coprime = false;
						}
					}
				} while(!coprime);

				do {
					coprime = true;
					for(auto z = incs.begin(); z != incs.end(); z++) {
						size_t c = j, d = *z;
						while(d) {
							size_t e = c % d;
							c = d;
							d = e;
						}
						if(c > 1) {
							j++;
							coprime = false;
						}
					}
				} while(!coprime);

			// pick coprime candidate closest to exact ratio
				if(x-i > j-x)
					i = j;
			}
			break;
		}

		case SHELL_E_COPRIME: {
		// Increment ratios of about 2.2 to 2.25 seem to work well,
		// e is about 2.7 which is a little higher.
		// Ensure all increments are mutually coprime using gcd.
			const double e1 = exp(1);
			size_t i = 7, j = 8;

			incs.push_back(1);

			while(i < n) {
				incs.push_back(i);

				double x = i * e1;
				i = floor(x);
				j = ceil(x);

				bool coprime;
				do {
					coprime = true;
					for(auto z = incs.begin(); z != incs.end(); z++) {
						size_t c = i, d = *z;
						while(d) {
							size_t e = c % d;
							c = d;
							d = e;
						}
						if(c > 1) {
							i--;
							coprime = false;
						}
					}
				} while(!coprime);

				do {
					coprime = true;
					for(auto z = incs.begin(); z != incs.end(); z++) {
						size_t c = j, d = *z;
						while(d) {
							size_t e = c % d;
							c = d;
							d = e;
						}
						if(c > 1) {
							j++;
							coprime = false;
						}
					}
				} while(!coprime);

			// pick coprime candidate closest to exact ratio
				if(x-i > j-x)
					i = j;
			}
			break;
		}

		case SHELL_PI_COPRIME: {
		// Increment ratios of about 2.2 to 2.25 seem to work well,
		// pi is about 3.14 which is significantly higher.
		// Ensure all increments are mutually coprime using gcd.
			const double pi = atan(1)*4;
			size_t i = 6, j = 6;

			incs.push_back(1);

			while(i < n) {
				incs.push_back(i);

				double x = i * pi;
				i = floor(x);
				j = ceil(x);

				bool coprime;
				do {
					coprime = true;
					for(auto z = incs.begin(); z != incs.end(); z++) {
						size_t c = i, d = *z;
						while(d) {
							size_t e = c % d;
							c = d;
							d = e;
						}
						if(c > 1) {
							i--;
							coprime = false;
						}
					}
				} while(!coprime);

				do {
					coprime = true;
					for(auto z = incs.begin(); z != incs.end(); z++) {
						size_t c = j, d = *z;
						while(d) {
							size_t e = c % d;
							c = d;
							d = e;
						}
						if(c > 1) {
							j++;
							coprime = false;
						}
					}
				} while(!coprime);

			// pick coprime candidate closest to exact ratio
				if(x-i > j-x)
					i = j;
			}
			break;
		}

		default:
		// devolve to insertion sort
		incs.push_back(1);
	}

	if(reverse) {
		// canonically return increments in ascending order
		for(size_t i=0, j=incs.size()-1; i < j; i++, j--)
			std::swap(incs[i], incs[j]);
	}

	return incs;
}

void ShellSort(SortArray& A, ShellSortIncrementType t)
{
	std::vector<size_t> incs = ShellSortIncrements(A.size(), t);

	while (!incs.empty())
	{
		size_t k = incs.back();

		incs.pop_back();

		for (size_t i = k; i < A.size(); i++)
		{
			value_type v = A[i];
			size_t j = i;

			while (j >= k && A[j-k] > v) {
				A.swap(j, j-k);
				j -= k;
			}
		}
	}
}

// ****************************************************************************
// *** Comb Sort

// from http://en.wikipediA.org/wiki/Comb_sort

void CombSort(SortArray& A)
{
	const double shrink = 1.3;
	size_t gap = A.size();

	while (gap > 1)
	{
		gap = (size_t)(gap / shrink);

		for (size_t i = 0; gap + i < A.size(); ++i)
			if (A[i] > A[i + gap])
				A.swap(i, i+gap);
	}

	// This prevents the end from looking like bubblesort.
	InsertionSort(A);
}

void CombSortPratt(SortArray& A)
{
	std::vector<size_t> gaps = ShellSortIncrements(A.size(), SHELL_1971_PRATT);

	do {
		size_t gap = gaps.back(); gaps.pop_back();

		for (size_t i = gap; i < A.size(); ++i)
			if (A[i] < A[i-gap])
				A.swap(i, i-gap);
	} while(gaps.size());
}

void CombSortFibonacci(SortArray& A)
{
	std::vector<size_t> gaps = ShellSortIncrements(A.size(), SHELL_FIBONACCI);

	do {
		size_t gap = gaps.back(); gaps.pop_back();
		if(gap == 1) break;

		for (size_t i = gap; i < A.size(); ++i)
			if (A[i] < A[i-gap])
				A.swap(i, i-gap);
	} while(gaps.size());

	// This prevents the end from looking like bubblesort.
	InsertionSort(A);
}

void GroomSort(SortArray& A)
{
	std::vector<size_t> gaps = ShellSortIncrements(A.size(), SHELL_FIBONACCI);

	do {
		size_t gap = gaps.back(); gaps.pop_back();
		size_t i;
		if(gap == 1) break;

		for (i = gap; i < A.size(); ++i)
			if (A[i] < A[i-gap])
				A.swap(i, i-gap);

		for (i = A.size() - gap; i > gap; i--)
			if (A[i] < A[i-gap])
				A.swap(i, i-gap);
	} while(gaps.size());

	// This prevents the end from looking like cocktail-shaker sort.
	InsertionSort(A);
}

