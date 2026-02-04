
#include "analysis.hpp"

#include <cstdio>

Curve fitCurve(const DoubleVec& X, const DoubleVec& Y)
{
	// y = a * x^b * ln^c(x) + d
	Curve crv = { 1,1,0,0 };
	size_t len = X.size();

	if(Y.size() != len) throw;

	// Precompute logarithms and means.
	DoubleVec LX, LLX, LY;
	double totLX = 0, totLY = 0;
	double meanLX, meanLY;
	LX.reserve(len);
	LLX.reserve(len);
	LY.reserve(len);

	for(size_t i=0; i < len; i++) {
		const double x = X[i], y = Y[i], lx = log(x), llx = log(lx), ly = log(y);
		totLX += lx;
		totLY += ly;
		LX.push_back(lx);
		LLX.push_back(llx);
		LY.push_back(ly);
	}

	meanLX = totLX / len;
	meanLY = totLY / len;

	// Start by obtaining an initial estimate for a and b, ignoring c and d.
	// Use a simple linear regression in log-space, so ln(y) = ln(a) + ln(x)*b.
	{
		double res1 = 0, res2 = 0;

		for(size_t i=0; i < len; i++) {
			double rlx = LX[i] - meanLX;
			double rly = LY[i] - meanLY;
			res1 += rlx * rly;
			res2 += rlx * rlx;
		}

		crv.b = res1 / res2;
		crv.a = exp(meanLY - crv.b * meanLX);
	}

//	printf("meanLX=%g meanLY=%g -- initial a=%g b=%g\n", meanLX, meanLY, crv.a, crv.b);

	// Refine all four parameters using gradient descent.
	// For multiplier a and exponents b and c, log-space is best:  ln(y) = ln(a) + ln(x)*b + ln(ln(x))*c
	// Weight samples by ln(x), to emphasise the asymptotic trend, rather than anomalous results for small arrays.
	// For linear parameter d, linear space is best.  Weight samplws by 1/ln(x) to reduce mutual dependence on exponential parameters.
	double da, db, dc, dd;
	static const double alearn = 0.0001, blearn = 0.0001, clearn = 0.001, dlearn = 0.01;
	do {
		da = db = dc = dd = 0;
		for(size_t i=0; i < len; i++) {
			const double x = X[i], lx = LX[i], llx = LLX[i], y = Y[i], ly = LY[i];
			const double cy = crv(x), cly = log(cy - crv.d);  // cy > 1 ? log(cy) : 0;
			const double ry = y - cy, rly = ly - cly;

			da += lx * rly;
			db += lx * rly * lx;
			dc += lx * rly * llx;
			dd += ry / lx;
		}
		da /= totLX;
		db /= totLX;
		dc /= totLX;
		dd /= len;

		crv.a += da * alearn;
		crv.b += db * blearn;
		crv.c += dc * clearn;
		crv.d += dd * dlearn;

//		printf("da=%18.8f db=%18.8f dc=%18.8f dd=%18.8f -- a=%18.8f b=%18.8f c=%18.8f d=%18.8f\r", da, db, dc, dd, crv.a, crv.b, crv.c, crv.d);
//		fflush(stdout);
	} while(fabs(da) + fabs(db) + fabs(dc) + fabs(dd) > 0.0001);

//	printf("\n");
	return crv;
}
