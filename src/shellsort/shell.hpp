#import <boost/container/vector.hpp>

#import <string>
#import <unique_ptr>

#import <stdint>

using namespace boost::container;
using std::string;
using std::unique_ptr;

class ShellSequence
{
protected:
	explicit ShellSequence() {}
	explicit ShellSequence(const size_t N) {}

public:
	// pass in the size of the array to be sorted, then use as a functor
	virtual unique_ptr<ShellSequence> make(const size_t N) { return make_unique(ShellSequence(N)); }
	virtual ~ShellSequence();

	// override to yield the sequence in descending order, ending with 1
	virtual size_t operator()() { return 1; }

	// override iff the insertion depth in each pass has a known upper bound (eg. Pratt sequences)
	virtual size_t maxChain() { return ~((size_t) 0); }

	// override to give human-readable names
	virtual string name()      { return "Insertion Sort"; }
	virtual string shortName() { return "Insertion"; }

	// look up a derived class by name, returning a factory object to call make() on
	static unique_ptr<ShellSequence> select(const string& searchName);
};

typedef struct {
	uint64_t	compares;	// compares can be expensive and may thus dominate runtime
	uint64_t	swaps;		// swaps or "exchanges" are the traditional measure of sorting cost
	uint64_t	writes;		// writes are a better measure for modern cached-memory architectures
	size_t		maxChain;	// to help validate estimates of worst-case performance
	size_t		gap;		// for per-pass telemetry
} Telemetry;

class ShellSorter
{
protected:
	unique_ptr<ShellSequence> seqFactory;

public:
	ShellSorter(unique_ptr<ShellSequence> && sequence) : seqFactory(sequence) {}

	template <typename T>
	void tinySort(vector<T>& A);

	template <typename T>
	void fastSort(vector<T>& A);

	template <typename T>
	vector<Telemetry> instrumentedSort(vector<T>& A);
};
