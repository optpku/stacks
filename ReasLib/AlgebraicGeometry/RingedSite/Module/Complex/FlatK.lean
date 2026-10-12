/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Flat
public import ReasLib.Algebra.Homology.CochainComplex.KFlat

/-!
# Termwise flatness and K-flatness

Termwise flatness and K-flatness are independent canonical predicates.  In particular, their
conjunction has no additional mathematical structure and should be written directly rather than
hidden behind a ringed-site-specific wrapper.
-/

@[expose] public section

open CategoryTheory

noncomputable section
