/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Homology
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tensor.HomologicalComplex.ProjectionFormula
public import ReasLib.Algebra.Homology.CochainComplex.KFlat
import Mathlib.Tactic.CrossRefAttribute

/-!
# K-flat complexes under extension of scalars

@stack 06Y1

For a homomorphism of commutative rings, extension of scalars preserves K-flat cochain
complexes.  The projection formula and the fact that restriction of scalars preserves and
reflects acyclicity are imported as the reusable proof infrastructure for this statement.
-/

@[expose] public section

noncomputable section

open CategoryTheory ComplexShape

universe u

namespace CochainComplex.IsKFlat

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Lemma 15.59.3 (06Y1), in the commutative-ring setting: extension of scalars preserves
K-flat cochain complexes. -/
@[stacks 06Y1 "extension of scalars preserves K-flat complexes"]
theorem extendScalars {K : CochainComplex (ModuleCat R) ℤ}
    (hK : K.IsKFlat) (f : R →+* S) :
    (((ModuleCat.extendScalars f).mapHomologicalComplex (up ℤ)).obj K).IsKFlat := sorry

end CochainComplex.IsKFlat
