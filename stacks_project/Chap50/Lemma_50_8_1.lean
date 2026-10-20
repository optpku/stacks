/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Kunneth.Comparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme.DeRham.Kunneth

variable {S X Y : Scheme.{u}}
variable (a : X ⟶ S) (b : Y ⟶ S)
variable (T : FiniteOrderDifferentialOperatorCat a ⥤
  FiniteOrderDifferentialOperatorCat b ⥤
    FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
variable (hT : IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
variable [T.PreservesZeroMorphisms] [∀ M, (T.obj M).PreservesZeroMorphisms]
variable [HomologicalComplex.HasMapBifunctor (operatorComplex a) (operatorComplex b) T (up ℕ)]
variable [HomologicalComplex.HasMapBifunctor
  (extendedOperatorComplex a) (extendedOperatorComplex b) T (up ℤ)]

/- Lemma 50.8.1: the canonical map
`Tot(Ωᵈᴿ[X/S] ⊠ Ωᵈᴿ[Y/S]) ⟶ Ωᵈᴿ[X ×_S Y/S]` is an isomorphism of
complexes of `(a ∘ pullback.fst a b)⁻¹ᴼᴿ_S`-modules. -/
@[stacks 0FMA] #check
  (AlgebraicGeometry.Scheme.DeRham.Kunneth.comparison_isIso (a := a) (b := b)
    (T := T) (hT := hT) :
      IsIso (AlgebraicGeometry.Scheme.DeRham.Kunneth.comparison a b T hT))

end Scheme.DeRham.Kunneth
end AlgebraicGeometry
