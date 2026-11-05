/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.DeltaFunctor
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Connecting Maps of Bounded-Below Right Derived Functors

This leaf exposes the connecting map directly between the degree functors
`RⁿF`. The comparison with the cohomological delta-functor presentation is
an explicit composite of associators, so no equality is converted into data
through `eqToHom`.
-/

open CategoryTheory
open scoped CategoryTheory

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.RightDerived.cohomological

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
  [RF.CommShift ℤ] [RF.IsTriangulated]

/-- The degree of the underlying cohomology family is explicitly isomorphic
to the corresponding bounded-below right-derived degree functor. -/
@[stacks 05TE "explicit degree comparison for a right-derived delta functor"]
noncomputable def degreeIso (n : ℕ) :
    ((RightDerived.delta RF).cohomologyFunctor
      (DerivedCategory.homologyFunctor B 0) (n : ℤ)).obj ≅
      RightDerived.degree RF (n : ℤ) :=
  Functor.associator
      (DerivedCategory.Plus.singleFunctor A 0 ⋙ RF)
      (DerivedCategory.Plus.ι : DerivedCategory.Plus B ⥤ DerivedCategory B)
      (DerivedCategory.homologyFunctor B (n : ℤ)) ≪≫
    Functor.associator
      (DerivedCategory.Plus.singleFunctor A 0) RF
      (DerivedCategory.Plus.homologyFunctor B (n : ℤ))

/-- The connecting map of the bounded-below right-derived degree functors,
obtained by conjugating the canonical homological connecting map by
`degreeIso`. -/
@[stacks 05TE "connecting map of bounded-below right-derived functors"]
noncomputable def connecting {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    (RightDerived.degree RF (n : ℤ)).obj S.X₃ ⟶
      (RightDerived.degree RF (n + 1 : ℕ)).obj S.X₁ :=
  (degreeIso RF n).inv.app S.X₃ ≫
    (RightDerived.delta RF).cohomologyConnecting
      (DerivedCategory.homologyFunctor B 0) hS n ≫
    (degreeIso RF (n + 1)).hom.app S.X₁

/-- The right-derived connecting map is natural in maps of short exact
complexes. -/
@[stacks 05TE "naturality of the right-derived connecting map"]
theorem connecting_naturality {S T : ShortComplex A}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) (n : ℕ) :
    CommSq ((RightDerived.degree RF (n : ℤ)).map φ.τ₃)
      (connecting RF hS n) (connecting RF hT n)
      ((RightDerived.degree RF (n + 1 : ℕ)).map φ.τ₁) := sorry

/-- The second map of a short exact sequence is annihilated by the
right-derived connecting map. -/
@[simp, reassoc, stacks 05TE "zero composite before a right-derived connecting map"]
theorem map_g_comp_connecting {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) :
    (RightDerived.degree RF (n : ℤ)).map S.g ≫ connecting RF hS n = 0 := sorry

/-- The right-derived connecting map is annihilated by the next first map. -/
@[simp, reassoc, stacks 05TE "zero composite after a right-derived connecting map"]
theorem connecting_comp_map_f {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) :
    connecting RF hS n ≫
      (RightDerived.degree RF (n + 1 : ℕ)).map S.f = 0 := sorry

end CategoryTheory.Functor.RightDerived.cohomological
