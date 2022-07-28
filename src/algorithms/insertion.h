/******************************************************************************
 * src/algorithms/insertion.h
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

void InsertionSort(class SortArray& a);
void BinaryInsertionSort(class SortArray& a);
void ExponentialInsertionSort(class SortArray& a);
void BlockInsertionSort(class SortArray& a);

void BubbleSort(class SortArray& a);
void CocktailShakerSort(class SortArray& a);
void GnomeSort(class SortArray& a);

enum ShellSortIncrementType {
	SHELL_1959_SHELL,
	SHELL_1960_FRANK,
	SHELL_1963_HIBBARD,
	SHELL_1965_PAPERNOV,
	SHELL_1971_PRATT,
	SHELL_1971_PRATT_35,
	SHELL_1971_PRATT_57,
	SHELL_1971_PRATT_711,
	SHELL_1973_KNUTH,
	SHELL_1982_SEDGEWICK,
	SHELL_1982_SEDGEWICK_MODIFIED,
	SHELL_1985_INCERPI,
	SHELL_1986_SEDGEWICK,
	SHELL_1991_GONNET,
	SHELL_1992_TOKUDA,
	SHELL_1996_JANSON_3PASS,
	SHELL_1996_JANSON_4PASS,
	SHELL_UNIFORM_3PASS,
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
	SHELL_FIBONACCI_CUBED,
	SHELL_LEONARDO,
	SHELL_LEONARDO_SQUARED,
	SHELL_LEONARDO_CUBED
};
extern ShellSortIncrementType g_shellsort_increment;

void ShellSort(SortArray& a, ShellSortIncrementType t);
void CombSort(class SortArray& a);
void CombSortPratt(class SortArray& a);
void CombSortFibonacci(class SortArray& a);
void GroomSort(class SortArray& a);

static inline void ShellSort(SortArray& A)					{ ShellSort(A, g_shellsort_increment); }
static inline void ShellSort_Shell59(SortArray& A)			{ ShellSort(A, SHELL_1959_SHELL); }
static inline void ShellSort_Frank60(SortArray& A)			{ ShellSort(A, SHELL_1960_FRANK); }
static inline void ShellSort_Hibbard63(SortArray& A)		{ ShellSort(A, SHELL_1963_HIBBARD); }
static inline void ShellSort_Papernov65(SortArray& A)		{ ShellSort(A, SHELL_1965_PAPERNOV); }
static inline void ShellSort_Pratt71(SortArray& A)			{ ShellSort(A, SHELL_1971_PRATT); }
static inline void ShellSort_Pratt71_35(SortArray& A)		{ ShellSort(A, SHELL_1971_PRATT_35); }
static inline void ShellSort_Pratt71_57(SortArray& A)		{ ShellSort(A, SHELL_1971_PRATT_57); }
static inline void ShellSort_Pratt71_711(SortArray& A)		{ ShellSort(A, SHELL_1971_PRATT_711); }
static inline void ShellSort_Knuth73(SortArray& A)			{ ShellSort(A, SHELL_1973_KNUTH); }
static inline void ShellSort_Sedgewick82(SortArray& A)		{ ShellSort(A, SHELL_1982_SEDGEWICK); }
static inline void ShellSort_Sedgewick82Mod(SortArray& A)	{ ShellSort(A, SHELL_1982_SEDGEWICK_MODIFIED); }
static inline void ShellSort_Incerpi85(SortArray& A)		{ ShellSort(A, SHELL_1985_INCERPI); }
static inline void ShellSort_Sedgewick86(SortArray& A)		{ ShellSort(A, SHELL_1986_SEDGEWICK); }
static inline void ShellSort_Gonnet91(SortArray& A)			{ ShellSort(A, SHELL_1991_GONNET); }
static inline void ShellSort_Tokuda92(SortArray& A)			{ ShellSort(A, SHELL_1992_TOKUDA); }
static inline void ShellSort_Janson96(SortArray& A)			{ ShellSort(A, SHELL_1996_JANSON_3PASS); }
static inline void ShellSort_Janson96Mod(SortArray& A)		{ ShellSort(A, SHELL_1996_JANSON_4PASS); }
static inline void ShellSort_Uniform3(SortArray& A)			{ ShellSort(A, SHELL_UNIFORM_3PASS); }
static inline void ShellSort_Ciura2001(SortArray& A)		{ ShellSort(A, SHELL_2001_CIURA); }
static inline void ShellSort_CiuraTokuda(SortArray& A)		{ ShellSort(A, SHELL_CIURA_TOKUDA); }
static inline void ShellSort_CiuraPratt(SortArray& A)		{ ShellSort(A, SHELL_CIURA_PRATT); }
static inline void ShellSort_CiuraFibonacci(SortArray& A)	{ ShellSort(A, SHELL_CIURA_FIBONACCI); }
static inline void ShellSort_CiuraFibonacci2(SortArray& A)	{ ShellSort(A, SHELL_CIURA_FIBONACCI2); }
static inline void ShellSort_CiuraFibonacci3(SortArray& A)	{ ShellSort(A, SHELL_CIURA_FIBONACCI3); }
static inline void ShellSort_CiuraRoot5(SortArray& A)		{ ShellSort(A, SHELL_CIURA_ROOT5); }
static inline void ShellSort_Root5_Coprime(SortArray& A)	{ ShellSort(A, SHELL_ROOT5_COPRIME); }
static inline void ShellSort_e_Coprime(SortArray& A)		{ ShellSort(A, SHELL_E_COPRIME); }
static inline void ShellSort_pi_Coprime(SortArray& A)		{ ShellSort(A, SHELL_PI_COPRIME); }
static inline void ShellSort_Fibonacci(SortArray& A)		{ ShellSort(A, SHELL_FIBONACCI); }
static inline void ShellSort_FibonacciSquared(SortArray& A)	{ ShellSort(A, SHELL_FIBONACCI_SQUARED); }
static inline void ShellSort_FibonacciCubed(SortArray& A)	{ ShellSort(A, SHELL_FIBONACCI_CUBED); }
static inline void ShellSort_Leonardo(SortArray& A)		{ ShellSort(A, SHELL_LEONARDO); }
static inline void ShellSort_LeonardoSquared(SortArray& A)	{ ShellSort(A, SHELL_LEONARDO_SQUARED); }
static inline void ShellSort_LeonardoCubed(SortArray& A)	{ ShellSort(A, SHELL_LEONARDO_CUBED); }
