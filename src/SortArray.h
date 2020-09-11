/*******************************************************************************
 * src/SortArray.h
 *
 * SortArray represents a simple array, which is displayed by WSortView to the
 * user is real-time.
 *
 *******************************************************************************
 * Copyright (C) 2014 Timo Bingmann <tb@panthema.net>
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
 ******************************************************************************/

#ifndef SORT_ARRAY_HEADER
#define SORT_ARRAY_HEADER

#include <vector>
#include <algorithm>
#include <stdlib.h>

#include <wx/log.h>
#include <wx/thread.h>
#include <wx/ctrlsub.h>

// ----------------------------------------------------------------------------

/// custom assertion (also active in release mode)
#define ASSERT(cond) do { if (!(cond)) {                \
	wxLogError(_("Assertion failed:\n%s in %s:%d"),     \
			   _T(#cond), _T(__FILE__), __LINE__);      \
	wxLog::FlushActive();                               \
	abort();                                            \
} } while(0)

// ----------------------------------------------------------------------------

/// globally count the number of comparisons done on value_type
extern size_t       g_compare_count;

/// globally count the number of array access
extern size_t       g_access_count;

// custom struct for array items, which allows detailed counting of comparisons.
class ArrayItem
{
public:
	typedef int value_type;

protected:
	value_type     value;

public:
	ArrayItem() {}

	explicit ArrayItem(const value_type& d) : value(d) {}

	ArrayItem(const ArrayItem& v) : value(v.value) {}

	constexpr ArrayItem& operator=(const ArrayItem&) = default;

	// ArrayItem has no implicit data cast, because most sorting algorithms use
	// comparisons. However, radix sort and similar use the following data
	// accessor. To add sound for these, we use a separate callback.
	const value_type& get() const
	{ OnAccess(*this); return value; }

	static void OnAccess(const ArrayItem& a);

	// for direct data access by visualizer
	const value_type& get_direct() const
	{ return value; }

	// *** comparisons

	bool operator== (const ArrayItem& v) const
	{ OnComparison(*this,v); return (value == v.value); }

	bool operator!= (const ArrayItem& v) const
	{ OnComparison(*this,v); return (value != v.value); }

	bool operator< (const ArrayItem& v) const
	{ OnComparison(*this,v); return (value < v.value); }

	bool operator<= (const ArrayItem& v) const
	{ OnComparison(*this,v); return (value <= v.value); }

	bool operator> (const ArrayItem& v) const
	{ OnComparison(*this,v); return (value > v.value); }

	bool operator>= (const ArrayItem& v) const
	{ OnComparison(*this,v); return (value >= v.value); }

	// ternary comparison which counts just one
	int cmp(const ArrayItem& v) const {
		OnComparison(*this,v);
		return (value == v.value ? 0 : value < v.value ? -1 : +1);
	}

	// *** comparisons without sound, counting or delay

	bool equal_direct(const ArrayItem& v) const
	{ return (value == v.value); }

	bool less_direct(const ArrayItem& v) const
	{ return (value < v.value); }

	bool greater_direct(const ArrayItem& v) const
	{ return (value > v.value); }
	int cmp_direct(const ArrayItem& v) const {
		return (value == v.value ? 0 : value < v.value ? -1 : +1);
	}

	static void OnComparison(const ArrayItem& a, const ArrayItem& b);
};

// ----------------------------------------------------------------------------

class SortDelay
{
public:

	/// central access function called by each array access of the algorithms
	virtual void OnAccess() = 0;
};

// ----------------------------------------------------------------------------

class SortArray
{
protected:
	// *** Displayed Array Data

	/// the array data
	std::vector<ArrayItem>     m_array;

	/// maximum value in array for scaling display
	ArrayItem::value_type      m_array_max;

	/// disable calculating of inversions
	bool m_calc_inversions;

	/// the number of inversions in the array order
	ssize_t m_inversions;

	/// access touch color
	struct Access
	{
		unsigned int index;
		unsigned short color;
		unsigned short sustain;
		unsigned short priority;

		Access(size_t i=0, unsigned short c=1,
			   unsigned short s=0, unsigned short p=0)
			: index(i), color(c), sustain(s), priority(p) { }
	};

	/// position of very last get/set accesses (two for swaps)
	Access      m_access1, m_access2;

	/// array of get/set accesses since last paint event
	std::vector<Access> m_access_list;

	/// custom markers in the array, set by algorithm
	std::vector<unsigned char>   m_mark;

	/// custom watched index pointers in the array, set by algorithm
	std::vector< std::pair<volatile ssize_t*,unsigned char> > m_watch;

	/// flag for sorted array
	bool        m_is_sorted;

	/// pointer to delay function
	SortDelay*  m_delay;

public:
	/// mutex for accesses and watch items
	wxMutex     m_mutex;

	// *** Array Functions

public:
	/// constructor
	SortArray();

	/// Set pointer to delay functional
	void SetSortDelay(SortDelay* delay) { m_delay = delay; }

	/// called by main when an algorithm starts
	void OnAlgoLaunch(const struct AlgoEntry& ae, bool withInversions = true);

	/// turn on/off calculation of inversions
	void SetCalcInversions(bool on);

	/// toggle boolean to calculate inversions
	void ToggleCalcInversions();

	/// fill the array with one of the predefined data templates
	void FillData(unsigned int schema, size_t arraysize);

	/// fill an array of strings with the list of predefined data templates
	static void FillInputlist(wxArrayString& list);

	/// return whether the array was sorted
	bool IsSorted() const { return m_is_sorted; }

	/// central access function called by each array access of the algorithms
	void OnAccess();

	/// check array after sorting algorithm
	bool CheckSorted();

	/// return the number of inversions in the array
	ssize_t GetInversions() const
	{ return m_inversions; }

	/// calculate the number of runs in the array
	size_t GetRuns() const;

public:
	/// reset the array to the given size
	void ResetArray(size_t size);

	/// called when the data fill function is finished
	void FinishFill();

	/// save access to array, forwards to sound system
	void SaveAccess(size_t i);

	/// check if index matches one of the watched pointers
	short InAccessList(ssize_t idx);

	/// check if index matches one of the watched pointers
	unsigned short InWatchList(ssize_t idx) const;

	/// Calculate the current color of the index i
	int GetIndexColor(size_t idx);

	/// recalculate the number of inversions (in quadratic time)
	void RecalcInversions();

	// update inversion count by calculating delta linearly for a replacement
	void AddInversions(size_t i);
	void DelInversions(size_t i);

	// update inversion count by calculating delta linearly for a swap
	void UpdateInversions(size_t i, size_t j);
	void RotateInversions(size_t i, size_t j, size_t k);

public:
	/// return array size
	size_t size() const { return m_array.size(); }

	/// return highest element value in array
	const ArrayItem::value_type& array_max() const
	{ return m_array_max; }

	/// Return an item of the array (bypassing sound, counting and delay)
	const ArrayItem& direct(size_t i) const
	{
		ASSERT(i < m_array.size());
		return m_array[i];
	}

	/// Return an item of the array (yields counting and delay)
	const ArrayItem& operator[](size_t i)
	{
		ASSERT(i < m_array.size());

		if (m_access1.index != i)
		{
			{
				wxMutexLocker lock(m_mutex);
				ASSERT(lock.IsOk());

				m_access1 = i;
				m_access_list.push_back(i);
			}

			// skip wait for duplicate accesses
			OnAccess();
		}

		return m_array[i];
	}

	/// Return a mutable item of the array (yields counting and delay)
	ArrayItem& get_mutable(size_t i)
	{
		ASSERT(i < m_array.size());

		if (m_access1.index != i)
		{
			{
				wxMutexLocker lock(m_mutex);
				ASSERT(lock.IsOk());

				m_access1 = i;
				m_access_list.push_back(i);
			}

			// skip wait for duplicate accesses
			OnAccess();
		}

		m_inversions = -1;	// can't predict what caller will do here

		return m_array[i];
	}

	/// Return an item of the array (yields delay, but no counting)
	const ArrayItem& get_nocount(size_t i)
	{
		ASSERT(i < m_array.size());

		if (m_access1.index != i)
		{
			{
				wxMutexLocker lock(m_mutex);
				ASSERT(lock.IsOk());

				m_access1 = i;
				m_access_list.push_back(i);
			}

			// skip wait for duplicate accesses
			--g_access_count;
			OnAccess();
		}

		return m_array[i];
	}

	/// Set an item of the array: first set then yield sound, counting and delay.
	void set(size_t i, const ArrayItem& v)
	{
		ASSERT(i < m_array.size());

		DelInversions(i);

		{
			wxMutexLocker lock(m_mutex);
			ASSERT(lock.IsOk());

			m_access1 = i;
			m_access_list.push_back(i);

			m_array[i] = v;
		}

		AddInversions(i);
		OnAccess();
	}

	/// Special function to swap the value in the array, this method provides a
	/// special visualization for this operation.
	void swap(size_t i, size_t j, bool withMarks=false)
	{
		ASSERT(i < m_array.size());
		ASSERT(j < m_array.size());

		if(i == j)
			return;

		{
			wxMutexLocker lock(m_mutex);
			ASSERT(lock.IsOk());

			m_access1 = i;
			m_access2 = j;

			m_access_list.push_back(i);
			m_access_list.push_back(j);
		}

		UpdateInversions(i, j); // update inversion count

		OnAccess();
		std::swap(m_array[i], m_array[j]);
		if(withMarks)
			mark_swap(i,j);
		OnAccess();
		m_access2 = -1;
	}

	/// Three, four, and five-way element rotations
	/// Push the first element along to displace the last, other elements move back
	/// Incurs one access per element
	void swap3(size_t i, size_t j, size_t k, bool withMarks=false)
	{
		ASSERT(i < m_array.size());
		ASSERT(j < m_array.size());
		ASSERT(k < m_array.size());

		if(i == j && j == k)
			return;
		if(i == j)
			return swap(j, k, withMarks);
		if(j == k)
			return swap(i, j, withMarks);

		const ArrayItem t = m_array[i];
		const unsigned char m = m_mark[i];

		m_mark[i] = m_mark[j];
		set(i, m_array[j]);

		m_mark[j] = m_mark[k];
		set(j, m_array[k]);

		m_mark[k] = m;
		set(k, t);
	}

	void swap4(size_t i, size_t j, size_t k, size_t p, bool withMarks=false)
	{
		ASSERT(i < m_array.size());
		ASSERT(j < m_array.size());
		ASSERT(k < m_array.size());
		ASSERT(p < m_array.size());

		if(i == j && j == k && k == p)
			return;
		if(i == j)
			return swap3(j, k, p, withMarks);
		if(j == k)
			return swap3(i, j, p, withMarks);
		if(k == p)
			return swap3(i, j, k, withMarks);

		const ArrayItem t = m_array[i];
		const unsigned char m = m_mark[i];

		m_mark[i] = m_mark[j];
		set(i, m_array[j]);

		m_mark[j] = m_mark[k];
		set(j, m_array[k]);

		m_mark[k] = m_mark[p];
		set(k, m_array[p]);

		m_mark[p] = m;
		set(p, t);
	}

	void swap5(size_t i, size_t j, size_t k, size_t p, size_t q, bool withMarks=false)
	{
		ASSERT(i < m_array.size());
		ASSERT(j < m_array.size());
		ASSERT(k < m_array.size());
		ASSERT(p < m_array.size());
		ASSERT(q < m_array.size());

		if(i == j && j == k && k == p && p == q)
			return;
		if(i == j)
			return swap4(j, k, p, q, withMarks);
		if(j == k)
			return swap4(i, j, p, q, withMarks);
		if(k == p)
			return swap4(i, j, k, q, withMarks);
		if(p == q)
			return swap4(i, j, k, p, withMarks);

		const ArrayItem t = m_array[i];
		const unsigned char m = m_mark[i];

		m_mark[i] = m_mark[j];
		set(i, m_array[j]);

		m_mark[j] = m_mark[k];
		set(j, m_array[k]);

		m_mark[k] = m_mark[p];
		set(k, m_array[p]);

		m_mark[p] = m_mark[q];
		set(p, m_array[q]);

		m_mark[q] = m;
		set(q, t);
	}

	/// Special function to efficiently swap two adjacent blocks in the array.
	/// This also swaps the marks associated with these values.
	/// This requires N array writes, half as many as using swaps.
	void rotate(size_t l, size_t m, size_t r)
	{
		const size_t b = m-l, a = r-m;
		if(!a || !b) return;

		RotateInversions(l,m,r);	// update inversion count

		if(a == b) {
			// blocks of equal size can simply be swapped
			for(size_t i=l, j=m; j < r; i++,j++) {
				m_access_list.push_back(i);
				m_access_list.push_back(j);
				m_access1 = i;
				m_access2 = j;
				OnAccess();
				std::swap(m_array[i], m_array[j]);
				std::swap(m_mark [i], m_mark [j]);
				OnAccess();
			}
		} else {
			// blocks of unequal size need to be "rotated"
			// compute GCD and LCM of block sizes
			size_t c=a, d=b;
			while(d) {
				size_t e = c % d;
				c = d;
				d = e;
			}
			d = (a+b)/c;

			for(size_t i=0; i < c; i++) {
				size_t x = (a+i)%(a+b);
				const ArrayItem t = m_array[x+l];

				m_access_list.push_back(x+l);
				m_access1 = x+l;
				OnAccess();

				for(size_t j=1; j < d; j++) {
					size_t y = (x+b)%(a+b);

					m_array[x+l] = m_array[y+l];
					std::swap(m_mark[x+l], m_mark[y+l]);

					m_access2 = y+l;
					m_access1 = x+l;
					m_access_list.push_back(x+l);
					OnAccess();
					x = y;
				}

				m_array[x+l] = t;
				m_access_list.push_back(x+l);
				m_access1 = x+l;
				OnAccess();
			}
		}

		m_access1 = m_access2 = -1;
	}

	/// Touch an item of the array: set color till next frame is outputted.
	void touch(size_t i, int color = 2,
			   unsigned short sustain = 0, unsigned short priority = 0)
	{
		ASSERT(i < m_array.size());

		{
			wxMutexLocker lock(m_mutex);
			ASSERT(lock.IsOk());

			m_access1 = Access(i, color, sustain, priority);
			m_access_list.push_back( Access(i, color, sustain, priority) );
		}
	}

	/// Mark an array index with a color.
	void mark(size_t i, int color = 2)
	{
		ASSERT(i < m_array.size());
		m_mark[i] = color;
	}

	/// Get mark, without dynamic effects
	int get_mark(size_t i)
	{
		ASSERT(i < m_array.size());
		return m_mark[i];
	}

	/// Swap color for two array indexes.
	void mark_swap(size_t i, size_t j)
	{
		ASSERT(i < m_array.size());
		ASSERT(j < m_array.size());

		std::swap(m_mark[i], m_mark[j]);
	}

	/// Unmark an array index.
	void unmark(size_t i)
	{
		ASSERT(i < m_array.size());
		m_mark[i] = 0;
	}

	/// Unmark all array indexes.
	void unmark_all()
	{
		m_access1 = m_access2 = -1;
		std::fill(m_mark.begin(), m_mark.end(), 0);

		wxMutexLocker lock(m_mutex);
		ASSERT(lock.IsOk());
		m_access_list.clear();
	}

	/// Highly experimental method to _track_ array live indexes. For this, the
	/// index must be marked volatile!.
	void watch(volatile ssize_t* idxptr, unsigned char color = 2)
	{
		wxMutexLocker lock(m_mutex);
		ASSERT(lock.IsOk());

		m_watch.push_back( std::make_pair(idxptr,color) );
	}

	/// Release all tracked live array indexes.
	void unwatch_all()
	{
		wxMutexLocker lock(m_mutex);
		ASSERT(lock.IsOk());

		m_watch.clear();
	}
};

// ----------------------------------------------------------------------------

#endif // SORT_ARRAY_HEADER
