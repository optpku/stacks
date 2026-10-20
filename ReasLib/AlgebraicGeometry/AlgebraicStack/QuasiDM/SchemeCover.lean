/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Object
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic stack is quasi-DM if and only if it admits a surjective,
flat, locally of finite presentation, locally quasi-finite morphism from a
scheme. -/
theorem isQuasiDM_iff_existsLocallyQuasiFiniteFlatCover {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    IsQuasiDM X ↔
      ∃ (W : Over S) (f : GroupoidsOver.slice W ⟶ X),
        Groupoids.Hom.Surjective f ∧ Groupoids.Hom.Flat f ∧
          Groupoids.Hom.LocallyOfFinitePresentation f ∧
          Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
