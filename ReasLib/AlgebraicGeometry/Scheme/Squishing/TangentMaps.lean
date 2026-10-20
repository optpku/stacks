/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Init
public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.Points

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open TopCat.Sheaf
open TopCat.Sheaf.Skyscraper
open scoped AlgebraicGeometry DualNumber

universe u

@[expose] public section

noncomputable section

namespace AlgebraicGeometry

/-- The coefficient of `ε` in a unit `a + bε` is `b`, while its logarithmic derivative is `b / a`.
This is the underlying function of the dlog map used on the right of the units sequence. -/
def dualNumberDlog {k : Type u} [Field k] (u : (DualNumber k)ˣ) : k :=
  u.val.snd / u.val.fst

/-- The dual-number local ring structure used to evaluate `vartheta` at its closed point. -/
instance dualNumber_isLocalRing {k : Type u} [Field k] : IsLocalRing (DualNumber k) := sorry

/-- A sheaf morphism to the dual-number skyscraper is the pullback induced by `vartheta` when
its map on the support stalk is the canonical map of the scheme morphism. -/
def IsTangentPullback
    {k : Type u} [Field k] [IsAlgClosed k]
    (X X' : SchemeOverField k) [Algebraic X] [Algebraic X']
    (f : X' ⟶ X)
    (vartheta : Spec (CommRingCat.of (DualNumber k)) ⟶ X'.left)
    (x : SchemeOverField.point k ⟶ X)
    (pullback : (TopCat.Sheaf.pushforward CommRingCat f.left.base).obj X'.left.sheaf ⟶
      pointRingSheaf X.left
        (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) (DualNumber k)) : Prop :=
  ∃ hpx : f.left (vartheta (IsLocalRing.closedPoint (DualNumber k))) =
      SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k),
    (TopCat.Presheaf.stalkFunctor CommRingCat
        (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k))).map pullback.hom ≫
        (stalkIsoOfSpecializes
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k))
          (CommRingCat.of (DualNumber k))
          (specializes_refl _)).hom =
      (((TopCat.Sheaf.pushforward CommRingCat f.left.base).obj X'.left.sheaf).presheaf.stalkCongr
        (Inseparable.of_eq hpx.symm)).hom ≫
        TopCat.Presheaf.stalkPushforward CommRingCat f.left.base X'.left.presheaf
          (vartheta (IsLocalRing.closedPoint (DualNumber k))) ≫
        Scheme.stalkClosedPointTo vartheta

/-- The canonical stalk characterization of `IsTangentPullback`. -/
theorem isTangentPullback_iff
    {k : Type u} [Field k] [IsAlgClosed k]
    {X X' : SchemeOverField k} [Algebraic X] [Algebraic X']
    {f : X' ⟶ X}
    {vartheta : Spec (CommRingCat.of (DualNumber k)) ⟶ X'.left}
    {x : SchemeOverField.point k ⟶ X}
    {pullback : (TopCat.Sheaf.pushforward CommRingCat f.left.base).obj X'.left.sheaf ⟶
      pointRingSheaf X.left
        (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) (DualNumber k)} :
    IsTangentPullback X X' f vartheta x pullback ↔
      ∃ hpx : f.left (vartheta (IsLocalRing.closedPoint (DualNumber k))) =
          SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k),
        (TopCat.Presheaf.stalkFunctor CommRingCat
            (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k))).map pullback.hom ≫
            (stalkIsoOfSpecializes
              (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k))
              (CommRingCat.of (DualNumber k))
              (specializes_refl _)).hom =
          (((TopCat.Sheaf.pushforward CommRingCat f.left.base).obj X'.left.sheaf).presheaf.stalkCongr
            (Inseparable.of_eq hpx.symm)).hom ≫
            TopCat.Presheaf.stalkPushforward CommRingCat f.left.base X'.left.presheaf
              (vartheta (IsLocalRing.closedPoint (DualNumber k))) ≫
            Scheme.stalkClosedPointTo vartheta := sorry

/-- The top-open component of a point skyscraper is propositionally the chosen ring. -/
theorem pointRingSheaf_top_eq {R : Type u} [hR : CommRing R] (X : Scheme.{u}) (x : X) :
    CommRingCat.of R =
      (pointRingSheaf X x R).1.obj (Opposite.op (⊤ : Opens X.toTopCat)) := sorry

/-- The corresponding additive component after forgetting the ring structure. -/
theorem pointRingSheaf_top_additive_eq {R : Type u} [hR : CommRing R] (X : Scheme.{u}) (x : X) :
    AddCommGrpCat.of R =
      (additiveSheaf (pointRingSheaf X x R)).1.obj
        (Opposite.op (⊤ : Opens X.toTopCat)) := sorry

/-- The dual-number section represented by an element on the top open of the point skyscraper. -/
noncomputable def dualNumberTopSection
    {k : Type u} [Field k] (X : Scheme.{u}) (x : X) (z : DualNumber k) :
    (additiveSheaf (pointRingSheaf X x (DualNumber k))).1.obj
      (Opposite.op (⊤ : Opens X.toTopCat)) :=
  (eqToHom (@pointRingSheaf_top_additive_eq (DualNumber k)
    TrivSqZeroExt.commRing X x)).hom z

/-- The scalar section represented by an element on the top open of the point skyscraper. -/
noncomputable def scalarTopSection
    {k : Type u} [Field k] (X : Scheme.{u}) (x : X) (a : k) :
    (additiveSheaf (pointRingSheaf X x k)).1.obj
      (Opposite.op (⊤ : Opens X.toTopCat)) :=
  (eqToHom (pointRingSheaf_top_additive_eq X x)).hom a

/-- The top-open dual-number section is the section represented by its coefficient value. -/
theorem dualNumberTopSection_def
    {k : Type u} [Field k] (X : Scheme.{u}) (x : X) (z : DualNumber k) :
    dualNumberTopSection X x z =
      (eqToHom (@pointRingSheaf_top_additive_eq (DualNumber k)
        TrivSqZeroExt.commRing X x)).hom z := sorry

/-- The top-open scalar section is the section represented by its scalar value. -/
theorem scalarTopSection_def
    {k : Type u} [Field k] (X : Scheme.{u}) (x : X) (a : k) :
    scalarTopSection X x a =
      (eqToHom (pointRingSheaf_top_additive_eq X x)).hom a := sorry

/-- Canonical pullback, coefficient, and dlog data attached to the tangent vector `vartheta`.
The two projection morphisms are specified against this same pullback, so the dlog arrow cannot
be chosen independently of the additive coefficient arrow. -/
structure SquishingTangentMaps
    {k : Type u} [Field k] [IsAlgClosed k]
    (X X' : SchemeOverField k) [Algebraic X] [Algebraic X']
    (f : X' ⟶ X)
    (vartheta : Spec (CommRingCat.of (DualNumber k)) ⟶ X'.left)
    (x : SchemeOverField.point k ⟶ X) where
  /-- The ring-sheaf pullback induced by `vartheta` and supported at `x`. -/
  varthetaPullback :
    (TopCat.Sheaf.pushforward CommRingCat f.left.base).obj X'.left.sheaf ⟶
      pointRingSheaf X.left
        (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) (DualNumber k)
  /-- The pullback agrees with the stalk map of the scheme morphism `vartheta`. -/
  varthetaPullback_spec : IsTangentPullback X X' f vartheta x varthetaPullback
  /-- The additive projection extracting the `ε`-coefficient from the dual-number skyscraper. -/
  coefficientProjection :
    additiveSheaf
        (pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) (DualNumber k)) ⟶
      additiveSheaf
        (pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k)
  /-- The units projection implementing `dlog (a + bε) = b / a` on the dual-number skyscraper. -/
  dlogProjection :
    CategoryTheory.Sheaf.unitsAddSheaf
        (pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) (DualNumber k)) ⟶
      additiveSheaf
        (pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k)
  /-- Naturality of the canonical `ε`-coefficient projection. -/
  coefficientProjection_spec :
    ∀ {V W : (Opens X.left)ᵒᵖ} (i : V ⟶ W) (s :
      (additiveSheaf
        (pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) (DualNumber k))).1.obj V),
      (additiveSheaf
        (pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k)).1.map i
          (coefficientProjection.hom.app V s) =
        coefficientProjection.hom.app W
          ((additiveSheaf
            (pointRingSheaf X.left
              (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) (DualNumber k))).1.map i s)
  /-- Naturality of the canonical logarithmic derivative projection. -/
  dlogProjection_spec :
    ∀ {V W : (Opens X.left)ᵒᵖ} (i : V ⟶ W) (s :
      (CategoryTheory.Sheaf.unitsAddSheaf
        (pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) (DualNumber k))).1.obj V),
      (additiveSheaf
        (pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k)).1.map i
          (dlogProjection.hom.app V s) =
        dlogProjection.hom.app W
          ((CategoryTheory.Sheaf.unitsAddSheaf
            (pointRingSheaf X.left
              (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) (DualNumber k))).1.map i s)
  /-- On the support, the coefficient projection sends `a + bε` to `b`. -/
  coefficientProjection_formula :
    ∀ z : DualNumber k,
      coefficientProjection.hom.app (Opposite.op ⊤)
          (dualNumberTopSection X.left
            (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) z) =
        scalarTopSection X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) z.snd
  /-- On the support, the dlog projection sends a unit to `b / a`. -/
  dlogProjection_formula :
    ∀ u : (DualNumber k)ˣ,
      dlogProjection.hom.app (Opposite.op ⊤)
          (CategoryTheory.Sheaf.unitsAddSheafSection
            (pointRingSheaf X.left
              (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) (DualNumber k))
            (Units.map
              (eqToHom (pointRingSheaf_top_eq X.left
                (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)))).hom.toMonoidHom u)) =
        scalarTopSection X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) (dualNumberDlog u)

/-- The canonical coefficient and logarithmic derivative projections satisfy their two support formulas. -/
theorem SquishingTangentMaps.projection_spec
    {k : Type u} [Field k] [IsAlgClosed k]
    {X X' : SchemeOverField k} [Algebraic X] [Algebraic X']
    {f : X' ⟶ X}
    {vartheta : Spec (CommRingCat.of (DualNumber k)) ⟶ X'.left}
    {x : SchemeOverField.point k ⟶ X}
    (maps : SquishingTangentMaps X X' f vartheta x) :
    (∀ z : DualNumber k,
      maps.coefficientProjection.hom.app (Opposite.op ⊤)
          (dualNumberTopSection X.left
            (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) z) =
        scalarTopSection X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) z.snd) ∧
    (∀ u : (DualNumber k)ˣ,
      maps.dlogProjection.hom.app (Opposite.op ⊤)
          (CategoryTheory.Sheaf.unitsAddSheafSection
            (pointRingSheaf X.left
              (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) (DualNumber k))
            (Units.map
              (eqToHom (pointRingSheaf_top_eq X.left
                (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)))).hom.toMonoidHom u)) =
        scalarTopSection X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) (dualNumberDlog u)) := sorry

/-- Construct canonical tangent maps from a pullback and its coefficient and dlog projections. -/
def SquishingTangentMaps.ofPullback
    {k : Type u} [Field k] [IsAlgClosed k]
    (X X' : SchemeOverField k) [Algebraic X] [Algebraic X']
    (f : X' ⟶ X)
    (vartheta : Spec (CommRingCat.of (DualNumber k)) ⟶ X'.left)
    (x : SchemeOverField.point k ⟶ X)
    (varthetaPullback :
      (TopCat.Sheaf.pushforward CommRingCat f.left.base).obj X'.left.sheaf ⟶
        pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) (DualNumber k))
    (varthetaPullback_spec : IsTangentPullback X X' f vartheta x varthetaPullback)
    (coefficientProjection :
      additiveSheaf
          (pointRingSheaf X.left
            (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) (DualNumber k)) ⟶
        additiveSheaf
          (pointRingSheaf X.left
            (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k))
    (dlogProjection :
      CategoryTheory.Sheaf.unitsAddSheaf
          (pointRingSheaf X.left
            (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) (DualNumber k)) ⟶
        additiveSheaf
          (pointRingSheaf X.left
            (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k))
    (coefficientProjection_spec : ∀ {V W : (Opens X.left)ᵒᵖ} (i : V ⟶ W) (s :
      (additiveSheaf
        (pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) (DualNumber k))).1.obj V),
      (additiveSheaf
        (pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k)).1.map i
          (coefficientProjection.hom.app V s) =
        coefficientProjection.hom.app W
          ((additiveSheaf
            (pointRingSheaf X.left
              (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) (DualNumber k))).1.map i s))
    (dlogProjection_spec : ∀ {V W : (Opens X.left)ᵒᵖ} (i : V ⟶ W) (s :
      (CategoryTheory.Sheaf.unitsAddSheaf
        (pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) (DualNumber k))).1.obj V),
      (additiveSheaf
        (pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k)).1.map i
          (dlogProjection.hom.app V s) =
        dlogProjection.hom.app W
          ((CategoryTheory.Sheaf.unitsAddSheaf
            (pointRingSheaf X.left
              (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) (DualNumber k))).1.map i s))
    (h_coefficientProjection_formula :
      ∀ z : DualNumber k,
        coefficientProjection.hom.app (Opposite.op ⊤)
            (dualNumberTopSection X.left
              (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) z) =
          scalarTopSection X.left
            (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) z.snd)
    (h_dlogProjection_formula :
      ∀ u : (DualNumber k)ˣ,
        dlogProjection.hom.app (Opposite.op ⊤)
            (CategoryTheory.Sheaf.unitsAddSheafSection
              (pointRingSheaf X.left
                (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) (DualNumber k))
              (Units.map
                (eqToHom (pointRingSheaf_top_eq X.left
                  (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)))).hom.toMonoidHom u)) =
          scalarTopSection X.left
            (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) (dualNumberDlog u)) :
    SquishingTangentMaps X X' f vartheta x :=
  { varthetaPullback := varthetaPullback
    varthetaPullback_spec := varthetaPullback_spec
    coefficientProjection := coefficientProjection
    dlogProjection := dlogProjection
    coefficientProjection_spec := coefficientProjection_spec
    dlogProjection_spec := dlogProjection_spec
    coefficientProjection_formula := h_coefficientProjection_formula
    dlogProjection_formula := h_dlogProjection_formula }

/-- The additive coefficient map induced by the canonical tangent pullback. -/
noncomputable def coefficientEvaluationOf
    {k : Type u} [Field k] [IsAlgClosed k]
    (X X' : SchemeOverField k) [Algebraic X] [Algebraic X']
    (f : X' ⟶ X)
    (vartheta : Spec (CommRingCat.of (DualNumber k)) ⟶ X'.left)
    (x : SchemeOverField.point k ⟶ X)
    (maps : SquishingTangentMaps X X' f vartheta x) :
    additiveSheaf
        ((TopCat.Sheaf.pushforward CommRingCat f.left.base).obj X'.left.sheaf) ⟶
      additiveSheaf
        (pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k) :=
  additiveSheafMap maps.varthetaPullback ≫ maps.coefficientProjection

/-- Normal form for the additive map induced by a canonical tangent pullback. -/
theorem coefficientEvaluationOf_def
    {k : Type u} [Field k] [IsAlgClosed k]
    (X X' : SchemeOverField k) [Algebraic X] [Algebraic X']
    (f : X' ⟶ X)
    (vartheta : Spec (CommRingCat.of (DualNumber k)) ⟶ X'.left)
    (x : SchemeOverField.point k ⟶ X)
    (maps : SquishingTangentMaps X X' f vartheta x) :
    coefficientEvaluationOf X X' f vartheta x maps =
      additiveSheafMap maps.varthetaPullback ≫ maps.coefficientProjection := sorry

/-- The units dlog map induced by the canonical tangent pullback. -/
noncomputable def dlogEvaluationOf
    {k : Type u} [Field k] [IsAlgClosed k]
    (X X' : SchemeOverField k) [Algebraic X] [Algebraic X']
    (f : X' ⟶ X)
    (vartheta : Spec (CommRingCat.of (DualNumber k)) ⟶ X'.left)
    (x : SchemeOverField.point k ⟶ X)
    (maps : SquishingTangentMaps X X' f vartheta x) :
    CategoryTheory.Sheaf.unitsAddSheaf
          ((TopCat.Sheaf.pushforward CommRingCat f.left.base).obj X'.left.sheaf) ⟶
        additiveSheaf
          (pointRingSheaf X.left
            (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k) :=
  CategoryTheory.Sheaf.unitsAddMap maps.varthetaPullback ≫ maps.dlogProjection

/-- Normal form for the units dlog map induced by a canonical tangent pullback. -/
theorem dlogEvaluationOf_def
    {k : Type u} [Field k] [IsAlgClosed k]
    (X X' : SchemeOverField k) [Algebraic X] [Algebraic X']
    (f : X' ⟶ X)
    (vartheta : Spec (CommRingCat.of (DualNumber k)) ⟶ X'.left)
    (x : SchemeOverField.point k ⟶ X)
    (maps : SquishingTangentMaps X X' f vartheta x) :
    dlogEvaluationOf X X' f vartheta x maps =
      CategoryTheory.Sheaf.unitsAddMap maps.varthetaPullback ≫ maps.dlogProjection := sorry

end AlgebraicGeometry

end
