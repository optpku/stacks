/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.NatRestriction
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Nonnegative

/-!
# Homology of the natural restriction of a chain DGA

This leaf lifts the generic comparison for a nonnegative integer-indexed chain complex to chain
DGAs.  The owner is independent of Tate resolutions, divided powers, and Koszul complexes, so
all three constructions can compare their natural and integer homology through the same API.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace ChainDGAlgebra

variable {R : Type u} [CommRing R]

/-- The homology of the natural restriction of a nonnegative chain DGA is canonically its
integer-graded homology in the corresponding degree. -/
@[stacks 09PQ "homology of the natural restriction of a nonnegative chain DGA"]
noncomputable def natRestrictionHomologyIso
    (A : ChainDGAlgebra.{u, v} R) [A.IsNonnegative] (n : ℕ) :
    A.natRestriction.homology n ≅ A.homology (n : ℤ) :=
  A.toChainComplex.natRestrictionHomologyIso n

/-- The natural-restriction homology comparison is natural in chain-DGA homomorphisms. -/
@[stacks 09PQ "naturality of chain-DGA natural-restriction homology"]
theorem Hom.natRestrictionHomologyIso_naturality
    {A B : ChainDGAlgebra.{u, v} R} [A.IsNonnegative] [B.IsNonnegative]
    (f : Hom A B) (n : ℕ) :
    HomologicalComplex.homologyMap f.natRestriction n ≫
        (B.natRestrictionHomologyIso n).hom =
      (A.natRestrictionHomologyIso n).hom ≫
        HomologicalComplex.homologyMap f.toChainMap (n : ℤ) := sorry

end ChainDGAlgebra
