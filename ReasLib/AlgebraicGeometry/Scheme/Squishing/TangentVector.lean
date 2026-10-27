/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

-- The local section calculations use the concrete units-sheaf representation.
import all ReasLib.Algebra.Category.Ring.Sheaf.Units
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
    (h : SquishesTangentVector X X' f vartheta x U tangentEvaluation maps) : IsFinite f.left :=
  h.finite

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
    IsClosedImmersion vartheta :=
  h.closedImmersion

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
    IsIso (f.left ∣_ U) :=
  h.restriction_isIso

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
        vartheta ≫ f.left) :=
  ⟨h.over_k, h.factors_through_point⟩

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
    IsFinite f.left ∧ IsIso (f.left ∣_ U) :=
  ⟨h.finite, h.restriction_isIso⟩

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
    (ShortComplex.mk (additiveStructureMap f.left) tangentEvaluation h.additive_zero).ShortExact :=
  ⟨h.additive_zero, h.additive_shortExact⟩

end SquishesTangentVector

/-- The dual-number logarithmic derivative is additive after multiplying units. -/
theorem dualNumberDlog_mul {k : Type u} [Field k]
    (u v : (DualNumber k)ˣ) :
    dualNumberDlog (u * v) = dualNumberDlog u + dualNumberDlog v := by
  have hu : u.val.fst ≠ 0 :=
    (TrivSqZeroExt.isUnit_iff_isUnit_fst.mp u.isUnit).ne_zero
  have hv : v.val.fst ≠ 0 :=
    (TrivSqZeroExt.isUnit_iff_isUnit_fst.mp v.isUnit).ne_zero
  simp only [dualNumberDlog, Units.val_mul, TrivSqZeroExt.snd_mul,
    TrivSqZeroExt.fst_mul, op_smul_eq_smul, smul_eq_mul]
  rw [div_add_div _ _ hu hv]
  congr 1
  simp only [mul_comm, add_comm]

private theorem squishingUnitsSection_eq {X : TopCat.{u}} (A : X.Sheaf CommRingCat.{u})
    {V : (Opens X)ᵒᵖ} (g : (A.1.obj V)ˣ) :
    CategoryTheory.Sheaf.unitsAddSheafSection A g = Additive.ofMul g := by
  change Function.invFun
    (fun s : Additive (A.1.obj V)ˣ => (Additive.toMul s).val) g.val = _
  exact Function.leftInverse_invFun (fun _ _ h => Units.ext h) (Additive.ofMul g)

private theorem squishingUnitsUnit_eq {X : TopCat.{u}} (A : X.Sheaf CommRingCat.{u})
    {V : (Opens X)ᵒᵖ} (g : (CategoryTheory.Sheaf.unitsAddSheaf A).1.obj V) :
    CategoryTheory.Sheaf.unitsAddSheafUnit A g = Additive.toMul g := by
  have hs : CategoryTheory.Sheaf.unitsAddSheafSection A =
      (Additive.ofMul : (A.1.obj V)ˣ → Additive (A.1.obj V)ˣ) := funext (squishingUnitsSection_eq A)
  change Function.invFun (CategoryTheory.Sheaf.unitsAddSheafSection A) g = _
  rw [hs]
  exact Function.leftInverse_invFun Function.injective_id (Additive.toMul g)

private theorem squishingUnitsMap_apply {X : TopCat.{u}} {A B : X.Sheaf CommRingCat.{u}}
    (f : A ⟶ B) (V : (Opens X)ᵒᵖ) (g : (CategoryTheory.Sheaf.unitsAddSheaf A).1.obj V) :
    (CategoryTheory.Sheaf.unitsAddMap f).hom.app V g =
      Additive.ofMul (Units.map (f.hom.app V).hom.toMonoidHom (Additive.toMul g)) := by
  change CategoryTheory.Sheaf.unitsAddSheafSection B
    (Units.map (f.hom.app V).hom.toMonoidHom (CategoryTheory.Sheaf.unitsAddSheafUnit A g)) = _
  rw [squishingUnitsUnit_eq, squishingUnitsSection_eq]
  rfl

private theorem pointRingSheaf_restriction_isIso (X : Scheme.{u}) (p : X) (R : Type u) [CommRing R]
    (V : X.Opens) (hx : p ∈ V) :
    IsIso ((pointRingSheaf X p R).1.map
      (homOfLE le_top : V ⟶ ⊤).op) := by
  classical
  change IsIso ((skyscraperPresheaf p (CommRingCat.of R)).map _)
  dsimp only [skyscraperPresheaf]
  simp only [hx, ↓reduceDIte]
  infer_instance

private theorem dualNumberTopSection_unit_val {k : Type u} [Field k] (X : Scheme.{u}) (p : X)
    (u : (DualNumber k)ˣ) :
    (Units.map (eqToHom (pointRingSheaf_top_eq X p)).hom.toMonoidHom u).val =
      dualNumberTopSection X p u.val := by
  have h : (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}).map
      (eqToHom (@pointRingSheaf_top_eq (DualNumber k)
        TrivSqZeroExt.commRing X p)) =
      eqToHom (@pointRingSheaf_top_additive_eq (DualNumber k)
        TrivSqZeroExt.commRing X p) := by
    exact eqToHom_map _ _
  exact congrArg (fun g => g.hom u.val) h

private theorem pointRingSheaf_sections_subsingleton_of_not_mem
    (X : Scheme.{u}) (p : X) (R : Type u) [CommRing R]
    (V : X.Opens) (hx : p ∉ V) :
    Subsingleton ((additiveSheaf
      (pointRingSheaf X p R)).1.obj (Opposite.op V)) := by
  classical
  change Subsingleton ((if p ∈ V then CommRingCat.of R else ⊤_ CommRingCat) : CommRingCat)
  rw [if_neg hx]
  exact CommRingCat.subsingleton_of_isTerminal CategoryTheory.Limits.terminalIsTerminal
private theorem squishingDlogProjection_eq_zero_of_coefficient
    {k : Type u} [Field k] [IsAlgClosed k]
    (X X' : SchemeOverField k) [Algebraic X] [Algebraic X']
    (f : X' ⟶ X)
    (vartheta : Spec (CommRingCat.of (DualNumber k)) ⟶ X'.left)
    (x : SchemeOverField.point k ⟶ X)
    (maps : SquishingTangentMaps X X' f vartheta x)
    (V : (Opens X.left)ᵒᵖ)
    (s : (CategoryTheory.Sheaf.unitsAddSheaf
      (pointRingSheaf X.left (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k))
        (DualNumber k))).1.obj V)
    (hs : maps.coefficientProjection.hom.app V (Additive.toMul s).val = 0) :
    maps.dlogProjection.hom.app V s = 0 := by
  classical
  let p := SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)
  let A := pointRingSheaf X.left p (DualNumber k)
  let B := pointRingSheaf X.left p k
  have htop (t : (CategoryTheory.Sheaf.unitsAddSheaf A).1.obj (Opposite.op ⊤))
      (ht : maps.coefficientProjection.hom.app (Opposite.op ⊤) (Additive.toMul t).val = 0) :
      maps.dlogProjection.hom.app (Opposite.op ⊤) t = 0 := by
    obtain ⟨u, hu⟩ := (Units.map_bijective
      (ConcreteCategory.bijective_of_isIso (eqToHom (pointRingSheaf_top_eq X.left p)))).surjective
        (Additive.toMul t)
    have hv : dualNumberTopSection X.left p u.val = (Additive.toMul t).val := by
      rw [← dualNumberTopSection_unit_val, hu]
      rfl
    have hcoeff : scalarTopSection X.left p u.val.snd = 0 := by
      rw [← maps.coefficientProjection_formula u.val, hv]
      exact ht
    have hsnd : u.val.snd = 0 := by
      apply (ConcreteCategory.bijective_of_isIso
        (eqToHom (pointRingSheaf_top_additive_eq X.left p))).injective
      simpa only [scalarTopSection, map_zero] using hcoeff
    have hrepr : CategoryTheory.Sheaf.unitsAddSheafSection A
        (Units.map (eqToHom (pointRingSheaf_top_eq X.left p)).hom.toMonoidHom u) = t := by
      rw [squishingUnitsSection_eq, hu]
      rfl
    rw [← hrepr, maps.dlogProjection_formula]
    change (eqToHom (pointRingSheaf_top_additive_eq X.left p)).hom
      (u.val.snd / u.val.fst) = 0
    rw [hsnd, zero_div]
    exact (eqToHom (pointRingSheaf_top_additive_eq X.left p)).hom.map_zero
  by_cases hx : p ∈ V.unop
  · let i : Opposite.op (⊤ : X.left.Opens) ⟶ V := (homOfLE le_top).op
    haveI : IsIso (A.1.map i) := pointRingSheaf_restriction_isIso X.left p (DualNumber k) V.unop hx
    haveI : IsIso (B.1.map i) := pointRingSheaf_restriction_isIso X.left p k V.unop hx
    obtain ⟨u, hu⟩ := (Units.map_bijective
      (ConcreteCategory.bijective_of_isIso (A.1.map i))).surjective (Additive.toMul s)
    let t : (CategoryTheory.Sheaf.unitsAddSheaf A).1.obj (Opposite.op ⊤) := Additive.ofMul u
    have hrestrict : (CategoryTheory.Sheaf.unitsAddSheaf A).1.map i t = s :=
      congrArg Additive.ofMul hu
    have hcoeff : maps.coefficientProjection.hom.app (Opposite.op ⊤) u.val = 0 := by
      apply (ConcreteCategory.bijective_of_isIso (B.1.map i)).injective
      have hval : A.1.map i u.val = (Additive.toMul s).val :=
        congrArg (fun v : (A.1.obj V)ˣ => v.val) hu
      exact (maps.coefficientProjection_spec i u.val).trans
        ((congrArg (maps.coefficientProjection.hom.app V) hval).trans
          (hs.trans (B.1.map i).hom.map_zero.symm))
    have hnat := congrArg (fun g => g t) (maps.dlogProjection.hom.naturality i)
    change maps.dlogProjection.hom.app V ((CategoryTheory.Sheaf.unitsAddSheaf A).1.map i t) =
      B.1.map i (maps.dlogProjection.hom.app (Opposite.op ⊤) t) at hnat
    rw [hrestrict, htop t hcoeff] at hnat
    exact hnat.trans (B.1.map i).hom.map_zero
  · exact @Subsingleton.elim (B.1.obj V)
      (pointRingSheaf_sections_subsingleton_of_not_mem X.left p k V.unop hx) _ _

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
        dlogEvaluationOf X X' f vartheta x maps = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  ext V s
  change maps.dlogProjection.hom.app V
    ((CategoryTheory.Sheaf.unitsAddMap maps.varthetaPullback).hom.app V
      ((unitsStructureMap f.left).hom.app V s)) = 0
  rw [squishingUnitsMap_apply, squishingUnitsMap_apply]
  apply squishingDlogProjection_eq_zero_of_coefficient X X' f vartheta x maps V
  have hz := h.additive_zero
  rw [h.tangentEvaluation_spec] at hz
  exact congrArg (fun g => g.hom.app V (Additive.toMul s).val) hz

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
