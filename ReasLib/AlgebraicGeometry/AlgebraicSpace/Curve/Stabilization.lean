/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.StableContraction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Prestable.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.StableDeligneMumford
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization

/-!
# Stabilization of prestable curves

Stabilization sends every prestable family of genus at least two to its stable
contraction, compatibly with isomorphisms and base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- A morphism from prestable genus-`g` curves to stable genus-`g` curves is a
stabilization if every family contracts to its image over their common base. -/
def IsStabilization {g : ℕ} {S : Scheme.{u}}
    (F : ofObjectProperty (prestableOfGenus g S) ⟶
      ofObjectProperty (stableOfGenus g S)) : Prop :=
  ∀ P : (prestableOfGenus g S).FullSubcategory,
    let Q := ((Groupoids.toFunctor F).obj P).obj
    let hbase : base Q = base P.obj :=
      congrArg (fun H => H.obj P) (Groupoids.comm F)
    let X := restrictOver (Over.mk (hom P.obj))
    let Y := restrictOver
      (Over.mk (hom Q ≫ SchemeRealization.ofOverMap (eqToHom hbase)))
    ∃ (c : X ⟶ Y)
      (hc : c ≫ SchemeRealization.toBase Y = SchemeRealization.toBase X),
      IsContractionToStable c hc

namespace IsStabilization

/-- A morphism is a stabilization exactly when every prestable family admits
a stable contraction to its functorial image, after restriction to its base. -/
theorem iff {g : ℕ} {S : Scheme.{u}}
    (F : ofObjectProperty (prestableOfGenus g S) ⟶
      ofObjectProperty (stableOfGenus g S)) :
    IsStabilization F ↔
      ∀ P : (prestableOfGenus g S).FullSubcategory,
        let Q := ((Groupoids.toFunctor F).obj P).obj
        let hbase : base Q = base P.obj :=
          congrArg (fun H => H.obj P) (Groupoids.comm F)
        let X := restrictOver (Over.mk (hom P.obj))
        let Y := restrictOver
          (Over.mk (hom Q ≫ SchemeRealization.ofOverMap (eqToHom hbase)))
        ∃ (c : X ⟶ Y)
          (hc : c ≫ SchemeRealization.toBase Y = SchemeRealization.toBase X),
          IsContractionToStable c hc :=
  Iff.rfl

end IsStabilization

/-- For genus at least two, there is a morphism from the stack of prestable
curves to the stack of stable curves sending every family to a stable
contraction over its base. -/
theorem exists_stabilization (g : ℕ) (hg : 2 ≤ g) (S : Scheme.{u}) :
    ∃ F : ofObjectProperty (prestableOfGenus g S) ⟶
        ofObjectProperty (stableOfGenus g S),
      IsStabilization F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
