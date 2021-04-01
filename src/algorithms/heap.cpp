/******************************************************************************
 * src/algorithms/heap.cpp
 *
 * Implementations of heap- and tree-based sorting algorithms.
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
#include "algorithms/heap.h"

// ****************************************************************************
// *** Heap Sort

// heavily adapted from http://www.codecodex.com/wiki/Heapsort

void HeapSort(SortArray& A)
{
	size_t n = A.size(), i = n / 2;

	// mark heap levels with different colors
	for (size_t j = i; j < n; ++j)
		A.mark(j, log(prevPowerOfTwo(j+1)) / log(2) + 4);

	while (1)
	{
		if (i > 0) {
			// build heap, sift A[i] down the heap
			i--;
		}
		else {
			// pop largest element from heap: swap front to back, and sift
			// front A[0] down the heap
			n--;
			if (n == 0) return;
			A.swap(0,n);

			A.mark(n);
			if (n+1 < A.size()) A.unmark(n+1);
		}

		size_t parent = i;
		size_t child = i*2 + 1;

		// sift operation - push the value of A[i] down the heap
		while (child < n)
		{
			if (child + 1 < n && A[child + 1] > A[child]) {
				child++;
			}
			if (A[child] > A[parent]) {
				A.swap(parent, child);
				parent = child;
				child = parent*2+1;
			}
			else {
				break;
			}
		}

		// mark heap levels with different colors
		A.mark(i, log(prevPowerOfTwo(i+1)) / log(2) + 4);
	}

}

// ****************************************************************************
// *** Smooth Sort

// from http://en.wikipediA.org/wiki/Smoothsort

namespace SmoothSortNS {

	static const int LP[] = {
		1, 1, 3, 5, 9, 15, 25, 41, 67, 109,
		177, 287, 465, 753, 1219, 1973, 3193, 5167, 8361, 13529, 21891,
		35421, 57313, 92735, 150049, 242785, 392835, 635621, 1028457,
		1664079, 2692537, 4356617, 7049155, 11405773, 18454929, 29860703,
		48315633, 78176337, 126491971, 204668309, 331160281, 535828591,
	866988873 // the next number is > 31 bits.
};

static void sift(SortArray& A, int pshift, int head)
{
	// we do not use Floyd's improvements to the heapsort sift, because we
	// are not doing what heapsort does - always moving nodes from near
	// the bottom of the tree to the root.

	value_type val = A[head];

	while (pshift > 1)
	{
		int rt = head - 1;
		int lf = head - 1 - LP[pshift - 2];

		if (val.cmp(A[lf]) >= 0 && val.cmp(A[rt]) >= 0)
			break;

		if (A[lf].cmp(A[rt]) >= 0) {
			A.set(head, A[lf]);
			head = lf;
			pshift -= 1;
		}
		else {
			A.set(head, A[rt]);
			head = rt;
			pshift -= 2;
		}
	}

	A.set(head, val);
}

static void trinkle(SortArray& A, int p, int pshift, int head, bool isTrusty)
{
	value_type val = A[head];

	while (p != 1)
	{
		int stepson = head - LP[pshift];

		if (A[stepson].cmp(val) <= 0)
			break; // current node is greater than head. sift.

		// no need to check this if we know the current node is trusty,
		// because we just checked the head (which is val, in the first
		// iteration)
		if (!isTrusty && pshift > 1) {
			int rt = head - 1;
			int lf = head - 1 - LP[pshift - 2];
			if (A[rt].cmp(A[stepson]) >= 0 ||
				A[lf].cmp(A[stepson]) >= 0)
				break;
		}

		A.set(head, A[stepson]);

		head = stepson;
		//int trail = Integer.numberOfTrailingZeros(p & ~1);
		int trail = __builtin_ctz(p & ~1);
		p >>= trail;
		pshift += trail;
		isTrusty = false;
	}

	if (!isTrusty) {
		A.set(head, val);
		sift(A, pshift, head);
	}
}

void sort(SortArray& A, int lo, int hi)
{
	int head = lo; // the offset of the first element of the prefix into m

	// These variables need a little explaining. If our string of heaps
	// is of length 38, then the heaps will be of size 25+9+3+1, which are
	// Leonardo numbers 6, 4, 2, 1.
	// Turning this into a binary number, we get b01010110 = 0x56. We represent
	// this number as a pair of numbers by right-shifting all the zeros and
	// storing the mantissa and exponent as "p" and "pshift".
	// This is handy, because the exponent is the index into L[] giving the
	// size of the rightmost heap, and because we can instantly find out if
	// the rightmost two heaps are consecutive Leonardo numbers by checking
	// (p&3)==3

	int p = 1; // the bitmap of the current standard concatenation >> pshift
	int pshift = 1;

	while (head < hi)
	{
		if ((p & 3) == 3) {
			// Add 1 by merging the first two blocks into a larger one.
			// The next Leonardo number is one bigger.
			sift(A, pshift, head);
			p >>= 2;
			pshift += 2;
		}
		else {
			// adding a new block of length 1
			if (LP[pshift - 1] >= hi - head) {
				// this block is its final size.
				trinkle(A, p, pshift, head, false);
			} else {
				// this block will get merged. Just make it trusty.
				sift(A, pshift, head);
			}

			if (pshift == 1) {
				// LP[1] is being used, so we add use LP[0]
				p <<= 1;
				pshift--;
			} else {
				// shift out to position 1, add LP[1]
				p <<= (pshift - 1);
				pshift = 1;
			}
		}
		p |= 1;
		head++;
	}

	trinkle(A, p, pshift, head, false);

	while (pshift != 1 || p != 1)
	{
		if (pshift <= 1) {
			// block of length 1. No fiddling needed
			//int trail = Integer.numberOfTrailingZeros(p & ~1);
			int trail = __builtin_ctz(p & ~1);
			p >>= trail;
			pshift += trail;
		}
		else {
			p <<= 2;
			p ^= 7;
			pshift -= 2;

			// This block gets broken into three bits. The rightmost bit is a
			// block of length 1. The left hand part is split into two, a block
			// of length LP[pshift+1] and one of LP[pshift].  Both these two
			// are appropriately heapified, but the root nodes are not
			// necessarily in order. We therefore semitrinkle both of them

			trinkle(A, p >> 1, pshift + 1, head - LP[pshift] - 1, true);
			trinkle(A, p, pshift, head - 1, true);
		}

		head--;
	}
}

} // namespace SmoothSortNS

void SmoothSort(SortArray& A)
{
	return SmoothSortNS::sort(A, 0, A.size()-1);
}

// ****************************************************************************
// *** Splay Sort

// Inserts all elements into a splay tree, then traverses that tree to discover
// the sorted order.  This takes O(n log n) operations and O(n) extra space.
// This implementation uses the semi-splay tree variant, and moves the data
// in-place for better visuals.

namespace Splay {
	typedef struct {
		size_t idx, parent, left, right;
	} SplayNode;

	class SplayTree {
	public:
		SortArray& data;
		std::vector<SplayNode> tree;
		size_t root;

		SplayTree(SortArray& A, size_t n=0) : data(A), root(0) {
			tree.reserve(n);
		}

		// rotates a node with its parent
		void rotate(size_t i) {
			size_t j = tree[i].parent;

			if(i == j) return;  // root node
			if(tree[j].left == i) {
				// left-hand rotation
				if(tree[i].right != i) {
					tree[j].left = tree[i].right;
					tree[tree[j].left].parent = j;
				} else {
					// no child here
					tree[j].left = j;
				}
				tree[i].right = j;

				if(tree[j].parent == j) {
					// parent is root, make ourselves root instead
					tree[i].parent = root = i;
				} else {
					size_t k = tree[i].parent = tree[j].parent;
					if(tree[k].left == j)
						tree[k].left = i;
					else
						tree[k].right = i;
				}
				tree[j].parent = i;
			} else {
				// right-hand rotation
				if(tree[i].left != i) {
					tree[j].right = tree[i].left;
					tree[tree[j].right].parent = j;
				} else {
					// no child here
					tree[j].right = j;
				}
				tree[i].left = j;

				if(tree[j].parent == j) {
					// parent is root, make ourselves root instead
					tree[i].parent = root = i;
				} else {
					size_t k = tree[i].parent = tree[j].parent;
					if(tree[k].left == j)
						tree[k].left = i;
					else
						tree[k].right = i;
				}
				tree[j].parent = i;
			}
		}

		// splays a node towards the root
		void splay(size_t i) {
			size_t j = tree[i].parent;
			size_t k = tree[j].parent;

			if(i == j) return;  // root node
			if(j == k) {
				// zig splay; rotate root's child to root
				rotate(i);
			} else if((tree[j].left == i && tree[k].left == j) || (tree[j].right == i && tree[k].right == j)) {
				// zig-zig semi-splay; rotate parent with grandparent, then continue with parent
				rotate(j);
				splay(j);
			} else {
				// zig-zag splay; rotate child with parent *and* with new parent after that, then continue
				rotate(i);
				rotate(i);
				splay(i);
			}
		}

		// iterates through the tree in order, without splaying
		size_t first(void) const {
			size_t i = root;
			while(tree[i].left != i)
				i = tree[i].left;
			return i;
		}
		size_t last(void) const {
			size_t i = root;
			while(tree[i].right != i)
				i = tree[i].right;
			return i;
		}
		size_t next(size_t i) const {
			if(tree[i].right != i) {
				// return leftmost child of right-hand child
				for(i = tree[i].right; i != tree[i].left; i = tree[i].left)
					;
				return i;
			} else while(1) {
				// back out one level of tree, if possible
				size_t j = tree[i].parent;
				if(j == i)
					return first(); // root node, wrap around
				if(tree[j].left == i)
					return j;       // parent is the next node

				// we're a right child, keep backing out
				i = j;
			}
		}
		size_t prev(size_t i) const {
			if(tree[i].left != i) {
				// return rightmost child of left-hand child
				for(i = tree[i].left; i != tree[i].right; i = tree[i].right)
					;
				return i;
			} else while(1) {
				// back out one level of tree, if possible
				size_t j = tree[i].parent;
				if(j == i)
					return last();  // root node, wrap around
				if(tree[j].right == i)
					return j;       // parent is the next node

				// we're a left child, keep backing out
				i = j;
			}
		}

		// locates an item from data[] in the tree, without splaying
		// assumes item is actually present, returns root node otherwise
		size_t find(size_t i) const {
			for(size_t j=0; j < tree.size(); j++)
				if(tree[j].idx == i)
					return j;
			return root;
		}

		// inserts an item from data[] into the tree, then splays it
		void insert(size_t i, const bool goingLeft=false) {
			size_t j = root;
			size_t k = tree.size();
			bool direction = false;
			SplayNode n;

			n.idx = i;
			n.parent = n.left = n.right = k;

			if(!k) {
				// adding first node
				tree.push_back(n);
				return;
			}

			do {
				n.parent = j;
				if(goingLeft) {
					direction = (data[i] <= data[tree[j].idx]);
				} else {
					direction = (data[i] <  data[tree[j].idx]);
				}
				if(direction)
					j = tree[j].left;
				else
					j = tree[j].right;
			} while(j != n.parent);

			// we've found a leaf branch
			(direction ? tree[j].left : tree[j].right) = k;
			tree.push_back(n);

			// now rebalance the tree
			splay(k);
		}

		// removes a node from the tree; this invalidates indices into the tree
		void remove(size_t i) {
			if(tree[i].left != i && tree[i].right != i) {
				// node has two children, so swap it with its neighbour (which must be a leaf), and delete that item instead
				size_t j = next(i);
				std::swap(tree[i].idx, tree[j].idx);
				i = j;

				j = tree[i].parent;
				if(tree[j].left == i)
					tree[j].left = j;
				else
					tree[j].right = j;
			} else if(tree[i].left != i) {
				// item has only a left child, so reparent it
				size_t j = tree[i].parent;
				size_t k = tree[i].left;

				if(j == i) {
					// we're the root node
					tree[k].parent = k;
					root = k;
				} else {
					tree[k].parent = j;
					if(tree[j].left == i)
						tree[j].left = k;
					else
						tree[j].right = k;
				}
			} else if(tree[i].right != i) {
				// item has only a right child, so reparent it
				size_t j = tree[i].parent;
				size_t k = tree[i].right;

				if(j == i) {
					// we're the root node
					tree[k].parent = k;
					root = k;
				} else {
					tree[k].parent = j;
					if(tree[j].left == i)
						tree[j].left = k;
					else
						tree[j].right = k;
				}
			} else {
				// item is a leaf; detach it from the tree
				size_t j = tree[i].parent;
				if(j == i) {
					// we're the root node, and also a leaf - nothing to do
				} else {
					// we were a leaf, now our parent forgets about us
					if(tree[j].left == i)
						tree[j].left = j;
					else
						tree[j].right = j;
				}
			}

			// node i is now an orphan; swap it to the end of the array for deletion
			size_t j = tree.size() - 1;
			if(i != j) {
				tree[i].idx = tree[j].idx;
				if(tree[j].left == j) {
					tree[i].left = i;
				} else {
					size_t k = tree[i].left = tree[j].left;
					tree[k].parent = i;
				}
				if(tree[j].right == j) {
					tree[i].right = i;
				} else {
					size_t k = tree[i].right = tree[j].right;
					tree[k].parent = i;
				}
				if(tree[j].parent == j) {
					tree[i].parent = i;
					root = i;
				} else {
					size_t k = tree[i].parent = tree[j].parent;
					if(tree[k].left == j)
						tree[k].left = i;
					else
						tree[k].right = i;
				}
			}

			tree.pop_back();
		}
	};

	// a conventional splaysort
	// insert all array elements into the tree, then traverse it in order
	void sort(SortArray& A, size_t l, size_t r) {
		SplayTree tree(A, r-l);
		std::vector<size_t> rev;

		// Build the splay tree
		rev.reserve(r-l);
		for(size_t i=l; i < r; i++) {
			tree.insert(i);
			rev.push_back(i-l);
		}

		// Iterate over the items in sorted order
		for(size_t i=tree.first(), j=l; j < r; j++, i = tree.next(i)) {
			size_t k = tree.tree[i].idx;

			// we want to swap the item into the correct position
			// but we also need to update the tree node of the item currently here
			// so that it points to the correct place after the swap
			// rev[] contains references from item position to tree position
			if(k != j) {
				size_t x = rev[j-l];  // j;

				if(tree.tree[x].idx != j) {
					// this shouldn't happen
					x = tree.find(j);
					tree.splay(x);
				}

				A.swap(j,k);
				A.mark_swap(j,k);

				tree.tree[x].idx = k;
				tree.tree[i].idx = j;

				rev[j-l] = i;
				rev[k-l] = x;
			}
		}
	}

	// a splay-tree accelerated version of cocktail-shaker sort
	// a search window of width m+1 (m defaults to sqrt(r-l)) is rolled back and forth
	// so up to m items can be carried along in a single pass, instad of just one
	// with m == r-l, this reduces to a plain splaysort
	// with m == 1, this reduces to a plain cocktail shaker sort
	void shake(SortArray& A, size_t l, size_t r, size_t m = 32) {
		if(!m) {
			while(m*m <= r-l)
				m++;
			m--;
		}
		SplayTree tree(A, m+1);
		size_t i=l, j=l, z=l;

		// begin by inserting first m elements into tree
		while(j < r && j-i < m) {
			tree.insert(j++);
		}

		while(r > l) {
			// ascending pass
			z = l;
			while(j < r) {
				// extend window to right
				tree.insert(j++, false);

				// move smallest item in window to the left edge
				size_t x = tree.first();
				size_t k = tree.tree[x].idx;

				if(k == j-1)
					z = i+1;  // item moving directly from right edge to left edge

				if(k != i) {
					size_t y = tree.find(i);

					A.swap(i,k);
					A.mark_swap(i,k);

					tree.tree[x].idx = i;
					tree.tree[y].idx = k;
				}

				// shrink window on the left
				tree.remove(x);
				i++;
			}

			// reduce iteration width on the right
			r = z;
			if(r <= l)
				break;

			// descending pass
			z = r;
			while(i-- > l) {
				// extend window to left
				tree.insert(i, true);

				// move largest item in window to the right edge
				j--;
				size_t x = tree.last();
				size_t k = tree.tree[x].idx;

				if(k == i)
					z = j;  // item moving directly from left edge to right edge

				if(k != j) {
					size_t y = tree.find(j);

					A.swap(j,k);
					A.mark_swap(j,k);

					tree.tree[x].idx = j;
					tree.tree[y].idx = k;
				}

				// shrink window on the right
				tree.remove(x);
			}
			i++;

			// reduce iteration width on the left
			l = z;
		}

		// ensure items in final window are correctly positioned
		while(i < j) {
			// move smallest item in window to the left edge
			size_t x = tree.first();
			size_t k = tree.tree[x].idx;
			if(k != i) {
				size_t y = tree.find(i);

				A.swap(i,k);
				A.mark_swap(i,k);

				tree.tree[x].idx = i;
				tree.tree[y].idx = k;
			}

			// shrink window on the left
			tree.remove(x);
			i++;
		}
	}

	// Collect a series of runs, as long as possible within the window size given.
	std::vector<size_t> runs(SortArray& A, size_t m = 32) {
		std::vector<size_t> out;
		SplayTree tree(A, m+1);
		size_t i,j,k;

		for(i=0, j=0, k=0; i < A.size(); i++) {
			// extend window to right
			tree.insert(i);

			// check whether we need to flush this run and start a new one
			if(j > k && tree.find(i) == tree.first() && A[i] < A[j-1]) {
				// flush
				tree.remove(tree.first());

				while(j < i) {
					size_t x = tree.first();
					size_t w = tree.tree[x].idx;
					if(w != j) {
						size_t y = tree.find(j);

						A.swap(j,w);
						A.mark_swap(j,w);

						tree.tree[x].idx = j;
						tree.tree[y].idx = w;
					}
					tree.remove(x);
					j++;
				}

				// start new run
				out.push_back(k);
				k = j;
				tree.insert(i);
			}

			// push any overflowing value out on the left
			if(i-j > m) {
				size_t x = tree.first();
				size_t w = tree.tree[x].idx;
				if(w != j) {
					size_t y = tree.find(j);

					A.swap(j,w);
					A.mark_swap(j,w);

					tree.tree[x].idx = j;
					tree.tree[y].idx = w;
				}
				tree.remove(x);
				j++;
			}
		}

		// flush final run
		while(j < i) {
			size_t x = tree.first();
			size_t w = tree.tree[x].idx;
			if(w != j) {
				size_t y = tree.find(j);

				A.swap(j,w);
				A.mark_swap(j,w);

				tree.tree[x].idx = j;
				tree.tree[y].idx = w;
			}
			tree.remove(x);
			j++;
		}

		out.push_back(k);
		out.push_back(A.size());

		return out;
	}
};

void SplaySort(SortArray& A)
{
	Splay::sort(A, 0, A.size());
}

void SplaySort(SortArray& A, size_t l, size_t r)
{
	Splay::sort(A, l, r);
}

void SplayShakeSort(SortArray& A)
{
	Splay::shake(A, 0, A.size());
}

void SplayShakeSort(SortArray& A, size_t m)
{
	Splay::shake(A, 0, A.size(), m);
}

std::vector<size_t> SplayCollectRuns(SortArray& A, size_t m)
{
	return Splay::runs(A, m);
}