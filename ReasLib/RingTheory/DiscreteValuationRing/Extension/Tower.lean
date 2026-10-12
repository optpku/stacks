/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Ramification
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Residue
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Towers of Discrete Valuation Ring Extensions

This module packages multiplicativity of ramification indices and residue
degrees in a tower. The composite extension instance is made explicit in each
statement, so the API does not require a global compositional instance.

@stack 0BRL
-/

universe u v w

open Ideal IsLocalRing

namespace IsExtensionOfDiscreteValuationRings

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsExtensionOfDiscreteValuationRings A B]
variable [IsExtensionOfDiscreteValuationRings B C]

/-- Lemma 15.112.3 (1): ramification indices multiply in a tower of extensions of discrete
valuation rings. -/
@[stacks 0BRL "(1), ramification index in a tower"]
theorem ramificationIndex_algebra_tower :
    let _ : IsExtensionOfDiscreteValuationRings A C := of_tower A B C
    ramificationIndex A C = ramificationIndex A B * ramificationIndex B C := sorry
-- Proof strategy: rewrite all three extension invariants with
-- `ramificationIndex_eq_ramificationIdx`, identify the contractions of the target maximal ideal
-- using the two DVR extension instances, and apply `Ideal.ramificationIdx_tower`; flatness of
-- `B → C` is supplied by the torsion-free module structure of a domain extension of a DVR.

/-- Lemma 15.112.3 (2): residue degrees multiply in a tower of finite residue-field extensions of
discrete valuation rings. -/
@[stacks 0BRL "(2), residue degree in a tower"]
theorem residueDegree_algebra_tower
    [FiniteDimensional (ResidueField A) (ResidueField B)]
    [FiniteDimensional (ResidueField B) (ResidueField C)] :
    let _ : IsExtensionOfDiscreteValuationRings A C := of_tower A B C
    let _ : FiniteDimensional (ResidueField A) (ResidueField C) :=
      FiniteDimensional.trans (ResidueField A) (ResidueField B) (ResidueField C)
    residueDegree A C = residueDegree A B * residueDegree B C := sorry
-- Proof strategy: unfold through `residueDegree_eq_finrank`, use the canonical residue-field
-- algebra tower induced by `A → B → C`, and apply `Module.finrank_mul_finrank` with the factors
-- reordered to match the displayed product.

end

end IsExtensionOfDiscreteValuationRings
