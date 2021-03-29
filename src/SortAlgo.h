/******************************************************************************
 * src/SortAlgo.h
 *
 * Implementations of many sorting algorithms.
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

#ifndef SORTALGO_H
#define SORTALGO_H

#include <wx/string.h>
#include "SortArray.h"

// *** List of Sorting Algorithms

struct AlgoEntry
{
	wxString name;
	void (*func)(class SortArray&);
	// maximum item count for test runs
	unsigned int max_testsize;
	// count inversions if n <= limit
	unsigned int inversion_count_limit;
	wxString text;
};

extern const struct AlgoEntry g_algolist[];
extern const size_t g_algolist_size;
extern const struct AlgoEntry* g_algolist_end;

// *** Sorting Algorithms

void SelectionSort(class SortArray& a);
void DualSelectionSort(class SortArray& a);
void CycleSort(class SortArray& a);

void InsertionSort(class SortArray& a);
void BinaryInsertionSort(class SortArray& a);

void MergeSort(class SortArray& a);
void MergeSortIterative(class SortArray& a);
void MergeSortInPlace(class SortArray& a);
void MergeSortSemiInPlace(class SortArray& a);
void SplayMergeSort(class SortArray& a);

void CataMergeSort(class SortArray& a);
void CataMergeSortStable(class SortArray& a);

wxArrayString QuickSortPivotText();

enum QuickSortPivotType { PIVOT_FIRST, PIVOT_LAST, PIVOT_MID, PIVOT_RANDOM, PIVOT_MEDIAN3, PIVOT_MEDIAN3_RANDOM, PIVOT_MEDIAN_MEDIANS };
extern QuickSortPivotType g_quicksort_pivot;

void QuickSortLR(class SortArray& a);
void QuickSortLL(class SortArray& a);
void QuickSortTernaryLR(class SortArray& a);
void QuickSortTernaryLL(class SortArray& a);
void QuickSortDualPivot(class SortArray& a);

void IntroSort(class SortArray& a);
void IntroSortDual(class SortArray& a);
void IntroSortDualStable(class SortArray& a);
void SeptenaryQuickSort(class SortArray& a);
void SeptenaryStableQuickSort(class SortArray& a);

void BubbleSort(class SortArray& a);
void CocktailShakerSort(class SortArray& a);
void GnomeSort(class SortArray& a);
void OddEvenSort(class SortArray& a);

wxArrayString ShellSortIncrementText();

enum ShellSortIncrementType {
	SHELL_1959_SHELL,
	SHELL_1960_FRANK,
	SHELL_1963_HIBBARD,
	SHELL_1965_PAPERNOV,
	SHELL_1971_PRATT,
	SHELL_1973_KNUTH,
	SHELL_1982_SEDGEWICK,
	SHELL_1985_INCERPI,
	SHELL_1986_SEDGEWICK,
	SHELL_1991_GONNET,
	SHELL_1992_TOKUDA,
	SHELL_2001_CIURA,
	SHELL_CIURA_TOKUDA,
	SHELL_CIURA_PRATT,
	SHELL_CIURA_FIBONACCI,
	SHELL_CIURA_FIBONACCI2,
	SHELL_CIURA_FIBONACCI3,
	SHELL_CIURA_ROOT5,
	SHELL_ROOT5_COPRIME,
	SHELL_E_COPRIME,
	SHELL_PI_COPRIME,
	SHELL_FIBONACCI,
	SHELL_FIBONACCI_SQUARED,
	SHELL_FIBONACCI_CUBED
};
extern ShellSortIncrementType g_shellsort_increment;

void ShellSort(SortArray& a, ShellSortIncrementType t);
void CombSort(class SortArray& a);
void CombSortPratt(class SortArray& a);
void CombSortFibonacci(class SortArray& a);
void GroomSort(class SortArray& a);

static inline void ShellSort(SortArray& A)             { ShellSort(A, g_shellsort_increment); }
static inline void ShellSort_Shell59(SortArray& A)     { ShellSort(A, SHELL_1959_SHELL); }
static inline void ShellSort_Frank60(SortArray& A)     { ShellSort(A, SHELL_1960_FRANK); }
static inline void ShellSort_Hibbard63(SortArray& A)   { ShellSort(A, SHELL_1963_HIBBARD); }
static inline void ShellSort_Papernov65(SortArray& A)  { ShellSort(A, SHELL_1965_PAPERNOV); }
static inline void ShellSort_Pratt71(SortArray& A)     { ShellSort(A, SHELL_1971_PRATT); }
static inline void ShellSort_Knuth73(SortArray& A)     { ShellSort(A, SHELL_1973_KNUTH); }
static inline void ShellSort_Sedgewick82(SortArray& A) { ShellSort(A, SHELL_1982_SEDGEWICK); }
static inline void ShellSort_Incerpi85(SortArray& A)   { ShellSort(A, SHELL_1985_INCERPI); }
static inline void ShellSort_Sedgewick86(SortArray& A) { ShellSort(A, SHELL_1986_SEDGEWICK); }
static inline void ShellSort_Gonnet91(SortArray& A)    { ShellSort(A, SHELL_1991_GONNET); }
static inline void ShellSort_Tokuda92(SortArray& A)    { ShellSort(A, SHELL_1992_TOKUDA); }
static inline void ShellSort_Ciura2001(SortArray& A)   { ShellSort(A, SHELL_2001_CIURA); }
static inline void ShellSort_CiuraTokuda(SortArray& A) { ShellSort(A, SHELL_CIURA_TOKUDA); }
static inline void ShellSort_CiuraPratt(SortArray& A)  { ShellSort(A, SHELL_CIURA_PRATT); }
static inline void ShellSort_CiuraFibonacci(SortArray& A)    { ShellSort(A, SHELL_CIURA_FIBONACCI); }
static inline void ShellSort_CiuraFibonacci2(SortArray& A)    { ShellSort(A, SHELL_CIURA_FIBONACCI2); }
static inline void ShellSort_CiuraFibonacci3(SortArray& A)    { ShellSort(A, SHELL_CIURA_FIBONACCI3); }
static inline void ShellSort_CiuraRoot5(SortArray& A)        { ShellSort(A, SHELL_CIURA_ROOT5); }
static inline void ShellSort_Root5_Coprime(SortArray& A)     { ShellSort(A, SHELL_ROOT5_COPRIME); }
static inline void ShellSort_e_Coprime(SortArray& A)         { ShellSort(A, SHELL_E_COPRIME); }
static inline void ShellSort_pi_Coprime(SortArray& A)        { ShellSort(A, SHELL_PI_COPRIME); }
static inline void ShellSort_Fibonacci(SortArray& A)         { ShellSort(A, SHELL_FIBONACCI); }
static inline void ShellSort_FibonacciSquared(SortArray& A)  { ShellSort(A, SHELL_FIBONACCI_SQUARED); }
static inline void ShellSort_FibonacciCubed(SortArray& A)    { ShellSort(A, SHELL_FIBONACCI_CUBED); }

void HeapSort(class SortArray& a);
void SmoothSort(class SortArray& a);
void SplaySort(class SortArray& a);
void SplaySort(class SortArray& A, size_t l, size_t r);
void SplayShakeSort(class SortArray& a);
void SplayShakeSort(class SortArray& a, size_t m);

void BitonicSort(SortArray& a);
void BitonicSortNetwork(SortArray& a);
void BatcherSortNetwork(SortArray& a);

void RadixSortLSD(class SortArray& a);
void RadixSortMSD(class SortArray& a);

void StlSort(class SortArray& a);
void StlStableSort(class SortArray& a);
void StlHeapSort(class SortArray& a);

void TimSort(class SortArray& a);
void WikiSort(class SortArray& a);

void BogoSort(class SortArray& a);
void BozoSort(class SortArray& a);
void StoogeSort(class SortArray& a);
void SlowSort(class SortArray& a);

// ****************************************************************************
// *** Iterator Adapter

// iterator based on http://zotu.blogspot.de/2010/01/creating-random-access-iterator.html

class MyIterator : public std::iterator<std::random_access_iterator_tag, ArrayItem>
{
protected:
	SortArray*  m_array;
	size_t      m_pos;

public:
	typedef std::iterator<std::random_access_iterator_tag, ArrayItem> base_type;

	typedef std::random_access_iterator_tag iterator_category;

	typedef base_type::value_type value_type;
	typedef base_type::difference_type difference_type;
	typedef base_type::reference reference;
	typedef base_type::pointer pointer;

	MyIterator() : m_array(NULL), m_pos(0) {}

	MyIterator(SortArray* A, size_t p) : m_array(A), m_pos(p) {}

	MyIterator(const MyIterator& r) : m_array(r.m_array), m_pos(r.m_pos) {}

	MyIterator& operator=(const MyIterator& r)
	{ m_array = r.m_array, m_pos = r.m_pos; return *this; }

	MyIterator& operator++()
	{ ++m_pos; return *this; }

	MyIterator& operator--()
	{ --m_pos; return *this; }

	MyIterator operator++(int)
	{ return MyIterator(m_array, m_pos++); }

	MyIterator operator--(int)
	{ return MyIterator(m_array, m_pos--); }

	MyIterator operator+(const difference_type& n) const
	{ return MyIterator(m_array, m_pos + n); }

	MyIterator& operator+=(const difference_type& n)
	{ m_pos += n; return *this; }

	MyIterator operator-(const difference_type& n) const
	{ return MyIterator(m_array, m_pos - n); }

	MyIterator& operator-=(const difference_type& n)
	{ m_pos -= n; return *this; }

	reference operator*() const
	{ return m_array->get_mutable(m_pos); }

	pointer operator->() const
	{ return &(m_array->get_mutable(m_pos)); }

	reference operator[](const difference_type& n) const
	{ return m_array->get_mutable(m_pos + n); }

	bool operator==(const MyIterator& r)
	{ return (m_array == r.m_array) && (m_pos == r.m_pos); }

	bool operator!=(const MyIterator& r)
	{ return (m_array != r.m_array) || (m_pos != r.m_pos); }

	bool operator<(const MyIterator& r)
	{ return (m_array == r.m_array ? (m_pos < r.m_pos) : (m_array < r.m_array)); }

	bool operator>(const MyIterator& r)
	{ return (m_array == r.m_array ? (m_pos > r.m_pos) : (m_array > r.m_array)); }

	bool operator<=(const MyIterator& r)
	{ return (m_array == r.m_array ? (m_pos <= r.m_pos) : (m_array <= r.m_array)); }

	bool operator>=(const MyIterator& r)
	{ return (m_array == r.m_array ? (m_pos >= r.m_pos) : (m_array >= r.m_array)); }

	difference_type operator+(const MyIterator& r2) const
	{ ASSERT(m_array == r2.m_array); return (m_pos + r2.m_pos); }

	difference_type operator-(const MyIterator& r2) const
	{ ASSERT(m_array == r2.m_array); return (m_pos - r2.m_pos); }
};


#endif // SORTALGO_H
