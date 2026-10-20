/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.ExtendNat
public import ReasLib.Algebra.Homology.CochainComplex.Nat.Bounded
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Kunneth.Complex
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Differentials
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatOver

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.Kunneth

variable {S X : Scheme.{u}}

/-- A relative differential form for a smooth morphism is flat over the base. -/
theorem operatorForm_isFlatOver (a : X ⟶ S) [Smooth a] (n : ℕ) :
    SheafOfModules.IsFlatOver
      (Scheme.Hom.FiniteOrderDifferentialOperatorCat.underlying a (operatorForm a n))
      a.toShHom := sorry

/-- Every term of the extended operator de Rham complex of a smooth morphism is flat over
the base. -/
theorem extendedOperatorComplex_isFlatOver (a : X ⟶ S) [Smooth a] (n : ℤ) :
    SheafOfModules.IsFlatOver
      (Scheme.Hom.FiniteOrderDifferentialOperatorCat.underlying a
        ((extendedOperatorComplex a).X n)) a.toShHom := sorry

/-- On a quasi-compact source, the nonnegative operator de Rham complex of a smooth morphism
is bounded above. -/
theorem operatorComplex_isBoundedAbove (a : X ⟶ S) [Smooth a] [CompactSpace X] :
    CochainComplex.Nat.IsBoundedAbove (operatorComplex a) := sorry

/-- Extension from nonnegative degrees makes the operator de Rham complex bounded below. -/
theorem extendedOperatorComplex_plus (a : X ⟶ S) :
    Fact (CochainComplex.plus (Scheme.Hom.FiniteOrderDifferentialOperatorCat a)
      (extendedOperatorComplex a)) := sorry

/-- For a smooth morphism with quasi-compact source, the extended operator de Rham complex
is bounded. -/
theorem extendedOperatorComplex_bounded (a : X ⟶ S) [Smooth a] [CompactSpace X] :
    Fact (CochainComplex.bounded (Scheme.Hom.FiniteOrderDifferentialOperatorCat a)
      (extendedOperatorComplex a)) := sorry

end AlgebraicGeometry.Scheme.DeRham.Kunneth
