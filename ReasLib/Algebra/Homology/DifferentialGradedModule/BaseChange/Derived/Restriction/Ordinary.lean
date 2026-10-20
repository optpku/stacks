/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.BaseChange.Derived.Restriction
public import ReasLib.Algebra.Homology.DifferentialGradedModule.DegreeZero
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The Base-Change Square in the Ordinary Derived Category

This leaf specializes the coefficient-DGA target of the derived restriction square to the
ordinary derived category of right modules over the coefficient ring.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace DifferentialGradedModule.BaseChange

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The top-then-right path in the base-change square, with the degree-zero coefficient DGA
identified with the ordinary derived category of right `S`-modules. -/
abbrev ordinaryRestrictedDerived (A : CochainDGAlgebra.{u, u} R) :
    CategoryTheory.Functor (DifferentialGradedModule.Derived.Category.{u, u} A)
      (DerivedCategory (ModuleCat.{u} (Sᵐᵒᵖ))) :=
  restrictedDerived (S := S) A ⋙ DifferentialGradedModule.DegreeZero.fromDerived R S

/-- The left-then-bottom path in the base-change square, with its target written as the
ordinary derived category of right `S`-modules. -/
abbrev ordinaryExtendedDerived (A : CochainDGAlgebra.{u, u} R) :
    CategoryTheory.Functor (DifferentialGradedModule.Derived.Category.{u, u} A)
      (DerivedCategory (ModuleCat.{u} (Sᵐᵒᵖ))) :=
  extendedDerived (S := S) A ⋙ DifferentialGradedModule.DegreeZero.fromDerived R S

/-- Lemma 22.33.8 (0BYZ) (2), in the source-facing target `D(S)`: extension to
`A ⊗[R] S` followed by restriction to `S` agrees canonically with restriction to `R` followed
by derived extension from `R` to `S`. -/
@[stacks 0BYZ "derived base-change square in the ordinary derived category"]
noncomputable def ordinaryRestrictionSquareIso (A : CochainDGAlgebra.{u, u} R) :
    ordinaryRestrictedDerived (S := S) A ≅ ordinaryExtendedDerived (S := S) A :=
  Functor.isoWhiskerRight (restrictionSquareIso (S := S) A)
    (DifferentialGradedModule.DegreeZero.fromDerived R S)

end DifferentialGradedModule.BaseChange
