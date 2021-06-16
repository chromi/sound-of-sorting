/******************************************************************************
 * src/algorithms/blockmerge.cpp
 *
 * Implementations of block-merge-based sorting algorithms.
 *
 * Note that these implementations may not be as good/fast as possible. Some
 * are modified so that the visualization is more instructive.
 *
 * Futhermore, some algorithms are annotated using the mark() and watch()
 * functions from SortArray. These functions add colors to the illustratation
 * and thereby makes the algorithm's visualization easier to explain.
 *
 ******************************************************************************
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
#include "algorithms/merge.h"

typedef std::vector<size_t> IdxVec;

/*
 * Block-Merge sorting algorithms are a family of stable, linearithmic-time merge sorts
 * with less than linear space complexity.  Several known examples are actually classed
 * as in-place:  Wikisort, Grail Sort, and Fransechini's Method.  Each of these, however,
 * incurs some implementation complexity and performance penalty to manage the tracking
 * state within the data to be sorted.
 *
 * This implementation of Block Merge Sort uses O(sqrt(N)) auxiliary space to simplify
 * state management and obtain high practical performance.  The goal is to achieve
 * similar performance to Timsort, with significantly less space overhead.
 */

// Merge adjacent runs from left, using an internal buffer for displaced left items.
// The ordering of the internal buffer is tracked using idx and rev auxiliaries, allocated by caller.
// We assume that trivial and easy cases have already been eliminated.
void MergeInternalForward(SortArray& A, IdxVec& idx, IdxVec& rev,
                          const size_t l, const size_t m, const size_t r)
{
	// The internal buffer may grow as large as the whole left buffer.
	ASSERT(m >= l && r >= m);
	const size_t a = m-l;
	ASSERT(a <= idx.size() && a <= rev.size());

	// Initialise internal buffer indices.
	for(size_t i=l, x=0; x < a; i++, x++) {
		idx[x] = i;
		rev[i % a] = x;
	}

	// Perform the merge.
	for(size_t i=l, j=m, x=0; i < j; i++) {
		if(j < r && A[idx[x]] > A[j]) {
			// use right item, displacing a left item
			const size_t y = rev[i % a];

			A.swap(i, j, true);
			A.mark(j, 12);	// left item now part of internal buffer

			idx[y] = j;
			rev[j % a] = y;
			j++;
		} else {
			// use left item
			if(idx[x] != i) {
				// left item is deep within internal buffer, move into place
				const size_t y = rev[i % a];

				A.swap(i, idx[x]);
				std::swap(idx[x], idx[y]);
				rev[idx[y] % a] = y;
			}

			A.mark(i, 4);	// left item in place
			x++;
		}
	}
}

// Merge adjacent runs from right, using an internal buffer for displaced right items.
// The ordering of the internal buffer is tracked using idx and rev auxiliaries, allocated by caller.
// We assume that trivial and easy cases have already been eliminated.
void MergeInternalBackward(SortArray& A, IdxVec& idx, IdxVec& rev,
                           const size_t l, const size_t m, const size_t r)
{
	// The internal buffer may grow as large as the whole right buffer.
	ASSERT(m >= l && r >= m);
	const size_t b = r-m;
	ASSERT(b <= idx.size() && b <= rev.size());

	// Initialise internal buffer indices.
	for(size_t i=r-1, x=0; x < b; i--, x++) {
		idx[x] = i;
		rev[i % a] = x;
	}

	// Perform the merge.
	for(size_t i=r-1, j=m-1, x=0; i > j; i--) {
		if(j > l && A[idx[x]] < A[j]) {
			// use left item, displacing a right item
			const size_t y = rev[i % a];

			A.swap(i, j, true);
			A.mark(j, 12);	// left item now part of internal buffer

			idx[y] = j;
			rev[j % a] = y;
			j--;
		} else {
			// use right item
			if(idx[x] != i) {
				// right item is deep within internal buffer, move into place
				const size_t y = rev[i % a];

				A.swap(i, idx[x]);
				std::swap(idx[x], idx[y]);
				rev[idx[y] % a] = y;
			}

			A.mark(i, 11);	// right item in place
			x++;
		}
	}
}

// Merge adjacent runs using block-merge technique and internal buffer for displaced left items.
// The ordering of the blocks is tracked using keys and blocks auxiliaries, allocated by caller.
// The ordering of the internal buffer is tracked using idx and rev auxiliaries, allocated by caller.
// We assume that trivial and easy cases have already been eliminated.
void MergeBlocks(SortArray& A, IdxVec& keys, IdxVec& idx, IdxVec& rev,
                 const size_t l, const size_t m, const size_t r)
{
	// We can handle as many blocks as in the keys/blocks index buffer, minus one.
	// Each block can be as large as the idx/rev index buffer.
	// One short block in each of the right/left runs can be accommodated without consuming a key slot.
	ASSERT(m >= l && r >= m);
	const size_t a = m-l, b = r-m, n = r-l;
	const size_t nKeys = std::min(keys.size(), rev.size()), bLen = std::min(idx.size(), rev.size());
	const size_t aKeys = a / bLen, bKeys = b / bLen, tKeys = aKeys + bKeys, aLeft = a % bLen, bLeft = b % bLen;
	ASSERT(tKeys < nKeys);

	// Begin by sorting entire blocks of length bLen by their leftmost element.
	// These blocks form a continuous sequence between l + a % bLen and r - b % bLen.
	// Because they initially form two sorted runs, we can use an efficient merge sort.
	// The "keys" buffer maps the original run order to the present block order.
	// The "rev" buffer maps the present block order to the original run order.
	for(size_t i=0; i <= tKeys; i++)
		keys[i] = rev[i] = i;

	for(size_t i=0, j=aKeys, k=0; k < tKeys; k++) {
		const size_t z = k * bLen + (aLeft + l);

		if(i < aKeys && j < tKeys) {
			// both right and left blocks available, pick the one that goes first
			const size_t x = keys[i] * bLen + (aLeft + l);
			const size_t y = keys[j] * bLen + (aLeft + l);

			// blocks should be sorted by the first element of left blocks and last element of right blocks
			if(A[x] > A[y + bLen - 1]) {
				// use left block
				if(keys[i] == k) continue;

				A.blockswap(z, x, bLen, true);
				rev[keys[i]] = rev[k];
				keys[rev[k]] = keys[i];
				rev[k] = i;
				keys[i++] = k;
			} else {
				// use right block
				if(keys[j] == k) continue;

				A.blockswap(z, y, bLen, true);
				rev[keys[j]] = rev[k];
				keys[rev[k]] = keys[j];
				rev[k] = j;
				keys[j++] = k;
			}
		} else if(i < aKeys) {
			// right blocks exhausted, just make sure remaining left blocks are in sequence
			if(keys[i] == k) continue;

			const size_t x = keys[i] * bLen + (aLeft + l);

			A.blockswap(z, x, bLen, true);
			rev[keys[i]] = rev[k];
			keys[rev[k]] = keys[i];
			rev[k] = i;
			keys[i++] = k;
		} else {
			// left blocks exhausted, just make sure remaining right blocks are in sequence
			if(keys[j] == k) continue;

			const size_t y = keys[j] * bLen + (aLeft + l);

			A.blockswap(z, y, bLen, true);
			rev[keys[j]] = rev[k];
			keys[rev[k]] = keys[j];
			rev[k] = j;
			keys[j++] = k;
		}
	}
	// The "rev" buffer can now be reused in the next stage of merging.

	// The elements are now arranged so that at most bLen left elements need to be displaced
	// temporarily into the internal buffer at any one time, in order to complete the merge.
	// The internal buffer uses the space just freed by the right element causing the displacement.

	// The "idx" circular buffer, inserting at x and removing at y, maps the original order
	// of the displaced elements to their actual position.  The "rev" buffer performs the
	// reverse mapping, and is itself indexed modulo bLen.  The z counter tracks how many elements
	// are currently displaced.
	// The internal buffer is pre-initialised to the first (a % bLen) left elements.
	size_t x=0, y=0, z=0;

	for(x=0; x < bLen; x++)
		idx[x] = rev[x] = 0;

	for(x=0; x < aLeft; x++, z++) {
		idx[x] = l + x;
		rev[idx[x] % bLen] = x;
		A.mark(l + x, 12);	// internally buffered left item
	}

	// The indices p and q refer to the next left and right blocks to be used, respectively.
	// The indices i and j refer to the next left and right elements *not* in the internal buffer,
	// and are incremented to the start of the p and q blocks when they run off the end of their
	// current blocks.  Index k refers to the current end of the merged section.
	size_t p = !(aLeft), q = aKeys+1;
	size_t i = keys[0]     * bLen + (aLeft + l);
	size_t j = keys[aKeys] * bLen + (aLeft + l);
	size_t k = l;

	while(k < r) {
		if(j >= r || (!z && A[i] <= A[j]) || (z && A[idx[x]] <= A[j])) {
			// take left element...
			if(z) {
				// ...from internal buffer
				if(idx[y] == k) {
					// already in place, shrink buffer
					A.mark(k, 4);	// left item
					y = (y+1) % bLen;
					z--;
				} else {
					// replace another left item, buffer stays same size
					A.swap(k, idx[y]);
					A.mark(k, 4);	// left item
					A.mark(k, 12);	// internally buffered left item
					idx[x] = idx[y];
					rev[idx[y] % bLen] = x;
					x = (x+1) % bLen;
					y = (y+1) % bLen;
				}
			} else {
				// left element already in place
				ASSERT(i == k);
				A.mark(k, 4);	// left item

				// advance left pointer, taking blocks into account
				i++;
				if((i - (aLeft + l)) % bLen == 0) {
					if(p >= aKeys)
						break;	// merge complete
					i = keys[p++];
				}
			}
		} else {
			// take right element
			if(j == k) {
				// unusually, right element already in place
				ASSERT(!z);
			} else {
				// displace left item into internal buffer
				A.swap(j, k, true);
				idx[x] = j;
				rev[j % bLen] = x;
				A.mark(j, 12);	// internally buffered left item
				x = (x+1) % bLen;
				z++;
				ASSERT(z <= bLen);
			}

			j++;
			if((j - (aLeft + l)) % bLen == 0) {
				j = keys[q++];
			}
		}
		k++;
	}
}

// Merge adjacent runs using either simple or block merge as appropriate.
// Checks for and resolves trivial merge cases first.
void MergeBlocksDriver(SortArray& A, IdxVec& keys, IdxVec& idx, IdxVec& rev,
                       const size_t l, const size_t m, const size_t r)
{
	// Either of the blocks is zero-length?
	if(m <= l || r <= m)
		return;

	// Mark elements of left and right runs for visualisation
	for(size_t i=l; i < m; i++)
		A.mark(i, 4);
	for(size_t i=m; i < r; i++)
		A.mark(i, 11);

	// Elements already in correct order?
	if(A[m-1] <= A[m])
		return;

	// Single-element blocks in wrong order?
	if(r-l == 2) {
		A.swap(l, m, true);
		return;
	}

	// Entire blocks need swapping?
	if(A[r-1] < A[l]) {
		A.rotate(l, m, r);
		return;
	}

	// TODO: also check for "easy" cases like Timsort does.

	// Perform the actual merge efficiently.
	if(idx.size() >= m-l && rev.size() >= m-l)
		MergeInternalForward(A, idx, rev, l, m, r);
	else if(idx.size() >= r-m && rev.size() >= r-m)
		MergeInternalBackward(A, idx, rev, l, m, r);
	else
		MergeBlocks(A, keys, idx, rev, l, m, r);
}

void BlockMergeIterative(SortArray& A)
{
	double n = A.size();
	size_t nKeys = floor(sqrt(n));
	size_t bLen  = ceil(n / nKeys);
	IdxVec keys(nKeys), idx(bLen), rev(std::max(nKeys,bLen));

	for(size_t s=1; s && s < A.size(); s *= 2) {
		for(size_t i=0; i < A.size(); i += s*2) {
			size_t j = i+s, k = j+s;

			if(j >= A.size())
				break;
			if(k > r)
				k = r;

			MergeBlocksDriver(A, keys, idx, rev, i, j, k);
		}
	}
}
