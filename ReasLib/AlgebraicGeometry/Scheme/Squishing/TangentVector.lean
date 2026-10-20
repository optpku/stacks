/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.AlgebraicGeometry.Scheme.Squishing.TangentMaps

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open TopCat.Sheaf
open TopCat.Sheaf.Skyscraper
open scoped AlgebraicGeometry DualNumber

universe u

@[expose] public section

noncomputable section

namespace AlgebraicGeometry
/-- A squishing datum consists of the geometric conditions and additive exactness
associated to a tangent vector and its canonical coefficient evaluation. -/
structure SquishesTangentVector
    {k : Type u} [Field k] [IsAlgClosed k]
    (X X' : SchemeOverField k) [Algebraic X] [Algebraic X']
    (f : X' ⟶ X)
    (vartheta : Spec (CommRingCat.of (DualNumber k)) ⟶ X'.left)
    (x : SchemeOverField.point k ⟶ X)
    (U : X.left.Opens)
    (tangentEvaluation : additiveSheaf
      ((TopCat.Sheaf.pushforward CommRingCat f.left.base).obj X'.left.sheaf) ⟶
        additiveSheaf
          (pointRingSheaf X.left
            (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k))
    (maps : SquishingTangentMaps X X' f vartheta x) : Prop where
  /-- The tangent vector is a closed immersion into `X'`. -/
  closedImmersion : IsClosedImmersion vartheta
  /-- The tangent vector is a morphism over the base field `k`. -/
  over_k :
    vartheta ≫ X'.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))
  /-- The composite with `f` factors through the chosen `k`-point `x`. -/
  factors_through_point :
    Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫
        SchemeOverField.rationalPoint x =
      vartheta ≫ f.left
  /-- The morphism `f` is finite. -/
  finite : IsFinite f.left
  /-- `U` is the complement of the rational point represented by `x`. -/
  complement :
    (U : Set X.left) =
      {SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)}ᶜ
  /-- The restriction of `f` over the complement of `x` is an isomorphism. -/
  restriction_isIso : IsIso (f.left ∣_ U)
  /-- The additive structure-sheaf sequence is a short exact sequence. -/
  additive_zero : additiveStructureMap f.left ≫ tangentEvaluation = 0
  /-- The additive structure-sheaf sequence is short exact. -/
  additive_shortExact :
    (ShortComplex.mk (additiveStructureMap f.left) tangentEvaluation additive_zero).ShortExact
  /-- The additive map is the `ε`-coefficient map induced by the canonical pullback. -/
  tangentEvaluation_spec :
    tangentEvaluation = coefficientEvaluationOf X X' f vartheta x maps

/-- Construct a squishing datum from its geometric conditions and canonical additive map. -/
def SquishesTangentVector.ofConditions
    {k : Type u} [Field k] [IsAlgClosed k]
    (X X' : SchemeOverField k) [Algebraic X] [Algebraic X']
    (f : X' ⟶ X)
    (vartheta : Spec (CommRingCat.of (DualNumber k)) ⟶ X'.left)
    (x : SchemeOverField.point k ⟶ X)
    (U : X.left.Opens)
    (tangentEvaluation :
      additiveSheaf
        ((TopCat.Sheaf.pushforward CommRingCat f.left.base).obj X'.left.sheaf) ⟶
      additiveSheaf
        (pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k))
    (maps : SquishingTangentMaps X X' f vartheta x)
    (closedImmersion : IsClosedImmersion vartheta)
    (over_k :
      vartheta ≫ X'.hom =
        Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))
    (factors_through_point :
      Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫
          SchemeOverField.rationalPoint x =
        vartheta ≫ f.left)
    (finite : IsFinite f.left)
    (complement :
      (U : Set X.left) =
        {SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)}ᶜ)
    (restriction_isIso : IsIso (f.left ∣_ U))
    (additive_zero : additiveStructureMap f.left ≫ tangentEvaluation = 0)
    (additive_shortExact :
      (ShortComplex.mk (additiveStructureMap f.left) tangentEvaluation additive_zero).ShortExact)
    (tangentEvaluation_spec :
      tangentEvaluation = coefficientEvaluationOf X X' f vartheta x maps) :
    SquishesTangentVector X X' f vartheta x U tangentEvaluation maps :=
  { closedImmersion := closedImmersion
    over_k := over_k
    factors_through_point := factors_through_point
    finite := finite
    complement := complement
    restriction_isIso := restriction_isIso
    additive_zero := additive_zero
    additive_shortExact := additive_shortExact
    tangentEvaluation_spec := tangentEvaluation_spec }


namespace SquishesTangentVector

/-- A squishing morphism is finite. -/
theorem toIsFinite
    {k : Type u} [Field k] [IsAlgClosed k]
    {X X' : SchemeOverField k} [Algebraic X] [Algebraic X']
    {f : X' ⟶ X} {vartheta : Spec (CommRingCat.of (DualNumber k)) ⟶ X'.left}
    {x : SchemeOverField.point k ⟶ X} {U : X.left.Opens}
    {tangentEvaluation :
      additiveSheaf ((TopCat.Sheaf.pushforward CommRingCat f.left.base).obj X'.left.sheaf) ⟶
        additiveSheaf
          (pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k)}
    (maps : SquishingTangentMaps X X' f vartheta x)
    (h : SquishesTangentVector X X' f vartheta x U tangentEvaluation maps) : IsFinite f.left := sorry

/-- The distinguished tangent vector is a closed immersion. -/
theorem toIsClosedImmersion
    {k : Type u} [Field k] [IsAlgClosed k]
    {X X' : SchemeOverField k} [Algebraic X] [Algebraic X']
    {f : X' ⟶ X} {vartheta : Spec (CommRingCat.of (DualNumber k)) ⟶ X'.left}
    {x : SchemeOverField.point k ⟶ X} {U : X.left.Opens}
    {tangentEvaluation :
      additiveSheaf ((TopCat.Sheaf.pushforward CommRingCat f.left.base).obj X'.left.sheaf) ⟶
        additiveSheaf
          (pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k)}
    (maps : SquishingTangentMaps X X' f vartheta x)
    (h : SquishesTangentVector X X' f vartheta x U tangentEvaluation maps) :
    IsClosedImmersion vartheta := sorry

/-- The punctured restriction in a squishing datum is an isomorphism. -/
theorem toIsIsoRestriction
    {k : Type u} [Field k] [IsAlgClosed k]
    {X X' : SchemeOverField k} [Algebraic X] [Algebraic X']
    {f : X' ⟶ X} {vartheta : Spec (CommRingCat.of (DualNumber k)) ⟶ X'.left}
    {x : SchemeOverField.point k ⟶ X} {U : X.left.Opens}
    {tangentEvaluation :
      additiveSheaf ((TopCat.Sheaf.pushforward CommRingCat f.left.base).obj X'.left.sheaf) ⟶
        additiveSheaf
          (pointRingSheaf X.left
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k)}
    (maps : SquishingTangentMaps X X' f vartheta x)
    (h : SquishesTangentVector X X' f vartheta x U tangentEvaluation maps) :
    IsIso (f.left ∣_ U) := sorry

/-- The map and factorization clauses of a squishing datum. -/
theorem map_spec
    {k : Type u} [Field k] [IsAlgClosed k]
    {X X' : SchemeOverField k} [Algebraic X] [Algebraic X']
    {f : X' ⟶ X}
    {vartheta : Spec (CommRingCat.of (DualNumber k)) ⟶ X'.left}
    {x : SchemeOverField.point k ⟶ X} {U : X.left.Opens}
    {tangentEvaluation :
      additiveSheaf ((TopCat.Sheaf.pushforward CommRingCat f.left.base).obj X'.left.sheaf) ⟶
        additiveSheaf
          (pointRingSheaf X.left
            (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k)}
    (maps : SquishingTangentMaps X X' f vartheta x)
    (h : SquishesTangentVector X X' f vartheta x U tangentEvaluation maps) :
      (vartheta ≫ X'.hom =
        Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))) ∧
      (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫
          SchemeOverField.rationalPoint x =
        vartheta ≫ f.left) := sorry

/-- The finiteness and punctured-isomorphism clauses of a squishing datum. -/
theorem finite_punctured_spec
    {k : Type u} [Field k] [IsAlgClosed k]
    {X X' : SchemeOverField k} [Algebraic X] [Algebraic X']
    {f : X' ⟶ X}
    {vartheta : Spec (CommRingCat.of (DualNumber k)) ⟶ X'.left}
    {x : SchemeOverField.point k ⟶ X} {U : X.left.Opens}
    {tangentEvaluation :
      additiveSheaf ((TopCat.Sheaf.pushforward CommRingCat f.left.base).obj X'.left.sheaf) ⟶
        additiveSheaf
          (pointRingSheaf X.left
            (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k)}
    (maps : SquishingTangentMaps X X' f vartheta x)
    (h : SquishesTangentVector X X' f vartheta x U tangentEvaluation maps) :
    IsFinite f.left ∧ IsIso (f.left ∣_ U) := sorry

/-- The additive short-exactness clauses of a squishing datum. -/
theorem additive_spec
    {k : Type u} [Field k] [IsAlgClosed k]
    {X X' : SchemeOverField k} [Algebraic X] [Algebraic X']
    {f : X' ⟶ X}
    {vartheta : Spec (CommRingCat.of (DualNumber k)) ⟶ X'.left}
    {x : SchemeOverField.point k ⟶ X} {U : X.left.Opens}
    {tangentEvaluation :
      additiveSheaf ((TopCat.Sheaf.pushforward CommRingCat f.left.base).obj X'.left.sheaf) ⟶
        additiveSheaf
          (pointRingSheaf X.left
            (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k)}
    (maps : SquishingTangentMaps X X' f vartheta x)
    (h : SquishesTangentVector X X' f vartheta x U tangentEvaluation maps) :
    (additiveStructureMap f.left ≫ tangentEvaluation = 0) ∧
    (ShortComplex.mk (additiveStructureMap f.left) tangentEvaluation h.additive_zero).ShortExact := sorry

end SquishesTangentVector

/-- The dual-number logarithmic derivative is additive after multiplying units. -/
theorem dualNumberDlog_mul {k : Type u} [Field k]
    (u v : (DualNumber k)ˣ) :
    dualNumberDlog (u * v) = dualNumberDlog u + dualNumberDlog v := sorry

/-- The canonical dlog map kills the image of the units structure sheaf under a squishing datum. -/
theorem dlogEvaluationOf_zero
    {k : Type u} [Field k] [IsAlgClosed k]
    (X X' : SchemeOverField k) [Algebraic X] [Algebraic X']
    (f : X' ⟶ X)
    (vartheta : Spec (CommRingCat.of (DualNumber k)) ⟶ X'.left)
    (x : SchemeOverField.point k ⟶ X)
    (U : X.left.Opens)
    (tangentEvaluation :
      additiveSheaf ((TopCat.Sheaf.pushforward CommRingCat f.left.base).obj X'.left.sheaf) ⟶
        additiveSheaf
          (pointRingSheaf X.left
            (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k))
    (maps : SquishingTangentMaps X X' f vartheta x)
    (h : SquishesTangentVector X X' f vartheta x U tangentEvaluation maps) :
    unitsStructureMap f.left ≫
        dlogEvaluationOf X X' f vartheta x maps = 0 := sorry

/-- Under a squishing datum, the units-sheaf map induced by logarithmic
derivative forms a short exact sequence. -/
theorem unitsShortExact_of_squishesTangentVector
    {k : Type u} [Field k] [IsAlgClosed k]
    (X X' : SchemeOverField k) [Algebraic X] [Algebraic X']
    (f : X' ⟶ X)
    (vartheta : Spec (CommRingCat.of (DualNumber k)) ⟶ X'.left)
    (x : SchemeOverField.point k ⟶ X)
    (U : X.left.Opens)
    (tangentEvaluation :
      additiveSheaf ((TopCat.Sheaf.pushforward CommRingCat f.left.base).obj X'.left.sheaf) ⟶
        additiveSheaf
          (pointRingSheaf X.left
            (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)) k))
    (maps : SquishingTangentMaps X X' f vartheta x)
    (h : SquishesTangentVector X X' f vartheta x U tangentEvaluation maps)
    :
    (ShortComplex.mk (unitsStructureMap f.left)
      (dlogEvaluationOf X X' f vartheta x maps)
      (dlogEvaluationOf_zero X X' f vartheta x U tangentEvaluation maps h)).ShortExact := sorry

end AlgebraicGeometry

end
