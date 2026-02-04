
#pragma once

#include <cmath>
#include <vector>

typedef std::vector<double> DoubleVec;

class Curve
{
public:
	// y = a * x^b * ln^c(x) + d
	double a, b, c, d;

	double operator()(const double x) const {
		return a * pow(x,b) * pow(log(x),c) + d;
	}
};

extern Curve fitCurve(const DoubleVec& X, const DoubleVec& Y);
