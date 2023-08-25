/**
 * @file CommandCell.cpp
 * @author dlinear
 * @date 22 Aug 2023
 * @copyright 2023 dlinear
 */

#include "CommandCell.h"

using std::ostream;

namespace dlinear {

// -------------
// AssertCommand
// -------------
ostream &AssertCommand::Display(ostream &os) const { return os << "(assert " << f_ << ")"; }

// -------------
// CheckSatCommand
// -------------
ostream &CheckSatCommand::Display(ostream &os) const { return os << "(check-sat)"; }

// -------------
// EchoCommand
// -------------
ostream &EchoCommand::Display(ostream &os) const { return os << "(echo " << message_ << ")"; }

// -------------
// ExitCommand
// -------------
ostream &ExitCommand::Display(ostream &os) const { return os << "(exit)"; }

// --------------------
// GetAssertionsCommand
// --------------------
ostream &GetAssertionsCommand::Display(ostream &os) const { return os << "(get-assertions)"; }

// --------------
// GetInfoCommand
// --------------
ostream &GetInfoCommand::Display(ostream &os) const { return os << "(get-info " << key_ << ")"; }

// --------------
// GetModelCommand
// --------------
ostream &GetModelCommand::Display(ostream &os) const { return os << "(get-model)"; }

// ----------------
// GetOptionCommand
// ----------------
ostream &GetOptionCommand::Display(ostream &os) const { return os << "(get-option " << key_ << ")"; }

// ---------------
// GetProofCommand
// ---------------
ostream &GetProofCommand::Display(ostream &os) const { return os << "(get-proof)"; }

// --------------------------
// GetUnsatAssumptionsCommand
// --------------------------
ostream &GetUnsatAssumptionsCommand::Display(ostream &os) const { return os << "(get-unsat-assumptions)"; }

// --------------------------
// GetUnsatCoreCommand
// --------------------------
ostream &GetUnsatCoreCommand::Display(ostream &os) const { return os << "(get-unsat-core)"; }

// ----------
// PopCommand
// ----------
ostream &PopCommand::Display(ostream &os) const { return os << "(pop " << level_ << ")"; }

// -----------
// PushCommand
// -----------
ostream &PushCommand::Display(ostream &os) const { return os << "(push " << level_ << ")"; }

// ------------
// ResetCommand
// ------------
ostream &ResetCommand::Display(ostream &os) const { return os << "(reset)"; }

// ----------------------
// ResetAssertionsCommand
// ----------------------
ostream &ResetAssertionsCommand::Display(ostream &os) const { return os << "(reset-assertions)"; }

// --------------
// SetInfoCommand
// --------------
ostream &SetInfoCommand::Display(ostream &os) const { return os << "(set-info " << key_ << " " << value_ << ")"; }

// ---------------
// SetLogicCommand
// ---------------
ostream &SetLogicCommand::Display(ostream &os) const { return os << "(set-logic " << logic_ << ")"; }

// ----------------
// SetOptionCommand
// ----------------
ostream &SetOptionCommand::Display(ostream &os) const { return os << "(set-option " << key_ << " " << value_ << ")"; }

}  // namespace dlinear
