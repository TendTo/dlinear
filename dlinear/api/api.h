/**
 * @file gmp.cpp
 * @author dlinear
 * @date 09 Aug 2023
 * @copyright 2023 dlinear
 * @brief Public api of dlinear.
 *
 * Provides an easy-to-use interface to dlinear and it's functionalities.
 */
#pragma once

#include <tl/optional.hpp>

#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Config.h"

namespace dlinear {

/**
 * Check the satisfiability of a given formula @p f with a given precision
 * @p delta.
 * @param f  Formula to check.
 * @param delta precision perturbation.
 * @return a model if @p f is δ-satisfiable or nullopt if @p f is unsatisfiable.
 */
tl::optional<Box> CheckSatisfiability(const Formula &f, double delta);

/**
 * Check the satisfiability of a given formula @p f with a given configuration
 * @p config.
 * @param f  Formula to check.
 * @param config configuration used to run the solver.
 * @return a model if @p f is δ-satisfiable or nullopt if @p f is unsatisfiable.
 */
tl::optional<Box> CheckSatisfiability(const Formula &f, const Config &config);

/**
 * Check the satisfiability of a given formula @p f with a given precision
 * @p delta.
 * @note We provide this version of API to avoid the use of optional.
 * @param f formula to check.
 * @param delta precision perturbation.
 * @param box box containing the model if @p f is δ-satisfiable.
 * @return whether @p f is δ-satisfiable.
 */
bool CheckSatisfiability(const Formula &f, double delta, Box *box);

/**
 * Check the satisfiability of a given formula @p f with a given configuration
 * @p config.
 * @param f formula to check.
 * @param config configuration used to run the solver.
 * @param box box containing the model if @p f is δ-satisfiable.
 * @return whether @p f is δ-satisfiable.
 */
bool CheckSatisfiability(const Formula &f, Config config, Box *box);

/**
 * Find a solution to minimize @p objective function while satisfying a
 * given @p constraint using @p delta.
 * @param objective objective function to minimize.
 * @param constraint constraint to satisfy.
 * @param delta precision perturbation.
 * @return a model if a solution exists or nullopt if there is no solution.
 */
tl::optional<Box> Minimize(const Expression &objective, const Formula &constraint, double delta);

/**
 * Find a solution to minimize @p objective function while satisfying a
 * given @p constraint using @p config.
 * @param objective objective function to minimize.
 * @param constraint constraint to satisfy.
 * @param config configuration used to run the solver.
 * @return a model if a solution exists or nullopt if there is no solution.
 */
tl::optional<Box> Minimize(const Expression &objective, const Formula &constraint, Config config);

/**
 * Find a solution to minimize @p objective function while satisfying a
 * given @p constraint using @p delta.
 * @note We provide this version of API to avoid the use of optional.
 * @param objective objective function to minimize.
 * @param constraint constraint to satisfy.
 * @param delta precision perturbation.
 * @param box box containing the model if a solution exists.
 * @return whether a solution exists.
 */
bool Minimize(const Expression &objective, const Formula &constraint, double delta, Box *box);

/**
 * Find a solution to minimize @p objective function while satisfying a
 * given @p constraint using @p config.
 * @note We provide this version of API to avoid the use of optional.
 * @param objective objective function to minimize.
 * @param constraint constraint to satisfy.
 * @param config configuration used to run the solver.
 * @param box box containing the model if a solution exists.
 * @return whether a solution exists.
 */
bool Minimize(const Expression &objective, const Formula &constraint, Config config, Box *box);

}  // namespace dlinear
