/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Restriction
public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle.NormalSheaf
public import ReasLib.AlgebraicGeometry.ChowGroup.ExteriorProduct
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative.Cycle
public import ReasLib.AlgebraicGeometry.Scheme.Module.Normal.Duality
public import ReasLib.RingTheory.CohenMacaulay.Ring
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-!
# Diagonal intersection products

The intersection product of Chow classes over a field is the cap of their exterior product
by the Gysin class of the diagonal. Proper intersections that are Cohen–Macaulay at their
expected-dimensional points have the associated cycle class of the scheme-theoretic intersection.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
open AlgebraicGeometry.Scheme.Modules hiding dual

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

variable {k : Type u} [Field k]

/-- The diagonal morphism of a scheme over a field, as a morphism in `Over (Spec k)`. -/
noncomputable abbrev diagonal (X : SchemeOverField k) : X ⟶ X ⨯ X :=
  prod.lift (𝟙 X) (𝟙 X)

/-- The Over-diagonal is the transport of `pullback.diagonal` along `prodLeftIsoPullback`. -/
theorem diagonal_left_eq (X : SchemeOverField k) :
    (diagonal X).left =
      pullback.diagonal X.hom ≫ (Over.prodLeftIsoPullback X X).inv := sorry

/-- The Over-diagonal is an immersion, as the transport of `pullback.diagonal`. -/
instance diagonal_isImmersion (X : SchemeOverField k) :
    IsImmersion (diagonal X).left := sorry

/-- The virtual normal bundle of the Over-diagonal, with module the normal sheaf and
quotient map the canonical biduality identification. -/
noncomputable def diagonalVirtualNormalBundle (X : SchemeOverField k)
    (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)] :
    VirtualNormalBundle (diagonal X).left :=
  ofNormalSheaf (diagonal X).left r (bidualityIso (diagonal X).left r)

/-- The module of the diagonal virtual normal bundle is the normal sheaf of the diagonal. -/
theorem diagonalVirtualNormalBundle_module (X : SchemeOverField k) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)] :
    (diagonalVirtualNormalBundle X r).module = normalSheaf (diagonal X).left := rfl

/-- Closed-specialization data for the coborder factorization of the Over-diagonal. -/
abbrev DiagonalSpecialization (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)] :=
  ClosedDeformation X.hom
    ((diagonal X).left.coborderRange.ι ≫ (X ⨯ X).hom)
    (diagonal X).left.liftCoborder
    (factorization_over X.hom (X ⨯ X).hom (diagonal X).left (Over.w (diagonal X))
      (diagonal X).left.liftCoborder (diagonal X).left.coborderRange.ι
      (diagonal X).left.liftCoborder_ι)
    (diagonalVirtualNormalBundle X r).toCoborder

/-- `DiagonalSpecialization` records a closed immersion followed by an open immersion. -/
theorem DiagonalSpecialization_spec (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r) :
    IsClosedImmersion (diagonal X).left.liftCoborder ∧
      IsOpenImmersion (diagonal X).left.coborderRange.ι := by
  exact ⟨inferInstance, inferInstance⟩

/-- The completed virtual-normal class of the Over-diagonal, formed from coborder
closed-specialization data. -/
noncomputable def diagonalCompletedClass (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r) :
    CompletedClass (fun _ ↦ (0 : ℤ)) X.hom (X ⨯ X).hom (diagonal X).left
      (Over.w (diagonal X)) (diagonalVirtualNormalBundle X r) :=
  composeClasses (fun _ ↦ (0 : ℤ)) X.hom (X ⨯ X).hom (diagonal X).left
    (Over.w (diagonal X)) (diagonal X).left.liftCoborder
    (diagonal X).left.coborderRange.ι (diagonal X).left.liftCoborder_ι
    (diagonalVirtualNormalBundle X r)
    (closedClass (fun _ ↦ (0 : ℤ)) X.hom
      ((diagonal X).left.coborderRange.ι ≫ (X ⨯ X).hom)
      (diagonal X).left.liftCoborder
      (factorization_over X.hom (X ⨯ X).hom (diagonal X).left (Over.w (diagonal X))
        (diagonal X).left.liftCoborder (diagonal X).left.coborderRange.ι
        (diagonal X).left.liftCoborder_ι)
      (diagonalVirtualNormalBundle X r).toCoborder D)

/-- `diagonalCompletedClass` is the coborder composition of the closed virtual-normal class. -/
theorem diagonalCompletedClass_def (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r) :
    diagonalCompletedClass X r D =
      composeClasses (fun _ ↦ (0 : ℤ)) X.hom (X ⨯ X).hom (diagonal X).left
        (Over.w (diagonal X)) (diagonal X).left.liftCoborder
        (diagonal X).left.coborderRange.ι (diagonal X).left.liftCoborder_ι
        (diagonalVirtualNormalBundle X r)
        (closedClass (fun _ ↦ (0 : ℤ)) X.hom
          ((diagonal X).left.coborderRange.ι ≫ (X ⨯ X).hom)
          (diagonal X).left.liftCoborder
          (factorization_over X.hom (X ⨯ X).hom (diagonal X).left
            (Over.w (diagonal X)) (diagonal X).left.liftCoborder
            (diagonal X).left.coborderRange.ι
            (diagonal X).left.liftCoborder_ι)
          (diagonalVirtualNormalBundle X r).toCoborder D) := rfl

/-- The Over-hom used by `diagonalGysinClass` is the categorical diagonal. -/
theorem diagonalGysinClass_overHom (X : SchemeOverField k) :
    overHom X.hom (X ⨯ X).hom (diagonal X).left (Over.w (diagonal X)) =
      diagonal X := by
  apply Over.OverMorphism.ext
  rfl

/-- The canonical degree-`r` Gysin class of the Over-diagonal, obtained as the rank-`r`
component of `diagonalCompletedClass`. -/
noncomputable def diagonalGysinClass (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r) :
    BivariantClass (fun _ ↦ 0) (diagonal X) (r : ℤ) :=
  (diagonalGysinClass_overHom X).symm ▸
  ((BivariantClass.OpenRestriction.Completion.globalEquiv (fun _ ↦ (0 : ℤ))
      (overHom X.hom (X ⨯ X).hom (diagonal X).left (Over.w (diagonal X)))
      (fun n : ℕ ↦ @rankOpen X.left (X ⨯ X).left (diagonal X).left
        (diagonal_isImmersion X) (diagonalVirtualNormalBundle X r) n)
      (fun _ : Unit ↦ (⊤ : (X ⨯ X).left.Opens)) (fun _ ↦ Unit.unit)
      (@Scheme.Modules.rankClopen_iSup X.left
        (diagonalVirtualNormalBundle X r).module
        (diagonalVirtualNormalBundle X r).isFiniteLocallyFree)
      (by simp; rfl)
      (@Scheme.Modules.rankClopen_pairwiseDisjoint X.left
        (diagonalVirtualNormalBundle X r).module
        (diagonalVirtualNormalBundle X r).isFiniteLocallyFree)
      (by intro a b h; exact (h (Subsingleton.elim a b)).elim)
      (fun n ↦ (@Scheme.Modules.rankClopen X.left
        (diagonalVirtualNormalBundle X r).module
        (diagonalVirtualNormalBundle X r).isFiniteLocallyFree n).isClopen)
      (fun _ ↦ isClopen_univ)
      (fun n ↦ rankOpen_le_preimage_top X.hom (X ⨯ X).hom (diagonal X).left
        (Over.w (diagonal X)) (diagonalVirtualNormalBundle X r) n))
    (diagonalCompletedClass X r D)).1 r

/-- The intersection product of Chow classes on a scheme over a field, obtained by capping
the exterior product with the canonical Gysin class of the diagonal. -/
noncomputable def intersectionProduct (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] {n m : ℤ} (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r)
    (alpha : RelativeChow (fun _ ↦ 0) X n)
    (beta : RelativeChow (fun _ ↦ 0) X m) :
    RelativeChow (fun _ ↦ 0) X (n + m - r) :=
  (diagonalGysinClass X r D).cap (𝟙 X) (diagonal X) (𝟙 (X ⨯ X))
    IsPullback.of_id_fst (n + m)
    (exteriorProductPairing X X n m alpha beta)

/-- The intersection product is the identity-square cap of the Chow exterior product by
the canonical diagonal Gysin class. -/
theorem intersectionProduct_def (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] {n m : ℤ} (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r)
    (alpha : RelativeChow (fun _ ↦ 0) X n)
    (beta : RelativeChow (fun _ ↦ 0) X m) :
    intersectionProduct X r D alpha beta =
      (diagonalGysinClass X r D).cap (𝟙 X) (diagonal X) (𝟙 (X ⨯ X))
        IsPullback.of_id_fst (n + m)
        (exteriorProductPairing X X n m alpha beta) := rfl

/-- For integral closed subschemes of an integral smooth scheme over a field, a proper
intersection whose two factor stalks are Cohen–Macaulay at every expected-dimensional point
has intersection product equal to the associated class of the scheme-theoretic intersection. -/
theorem intersectionProduct_eq_associatedCycle
    (X : SchemeOverField k) [IsIntegral X.left] [Smooth X.hom]
    (Y Z : X.left.IdealSheafData)
    [IsIntegral Y.subscheme] [IsIntegral Z.subscheme]
    {nX nY nZ : ℤ} {r : ℕ}
    (hnX : nX = X.hom.relativeDimensionFunction (fun _ ↦ 0) (genericPoint X.left))
    (hnY : nY = X.hom.relativeDimensionFunction (fun _ ↦ 0)
      (Y.subschemeι (genericPoint Y.subscheme)))
    (hnZ : nZ = X.hom.relativeDimensionFunction (fun _ ↦ 0)
      (Z.subschemeι (genericPoint Z.subscheme)))
    (hr : nX = r)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r)
    (h_dim : X.hom.closedSubschemeDeltaDimension (fun _ ↦ 0) (Y ⊔ Z) ≤
      (nY + nZ - (r : ℤ) : EInt))
    (h_CM : ∀ ξ : (Y ⊔ Z).subscheme,
      X.hom.relativeDimensionFunction (fun _ ↦ 0) ((Y ⊔ Z).subschemeι ξ) =
          nY + nZ - nX →
        CohenMacaulayRing
            (Y.subscheme.presheaf.stalk
              (Scheme.IdealSheafData.inclusion (le_sup_left : Y ≤ Y ⊔ Z) ξ)) ∧
          CohenMacaulayRing
            (Z.subscheme.presheaf.stalk
              (Scheme.IdealSheafData.inclusion (le_sup_right : Z ≤ Y ⊔ Z) ξ))) :
    intersectionProduct X r D (RelativeChow.closedSubschemeClass (fun _ ↦ 0) X Y nY)
        (RelativeChow.closedSubschemeClass (fun _ ↦ 0) X Z nZ) =
      RelativeChow.closedSubschemeClass (fun _ ↦ 0) X (Y ⊔ Z) (nY + nZ - (r : ℤ)) := sorry

/-- The diagonal of a smooth scheme over a field has finite locally free conormal sheaf. -/
@[instance]
theorem diagonal_conormal_isFiniteLocallyFree (X : SchemeOverField k) [Smooth X.hom] :
    IsFiniteLocallyFree (conormalSheaf (diagonal X).left) := sorry

/-- The normal virtual bundle of the diagonal of a smooth scheme, using canonical
biduality and allowing locally varying rank. -/
noncomputable def diagonalVirtualNormalBundleOfRankLoci (X : SchemeOverField k)
    [Smooth X.hom] : VirtualNormalBundle (diagonal X).left :=
  ofNormalSheafOfRankLoci (diagonal X).left

/-- A chosen model of deformation to the normal cone of the diagonal, factored through
its coborder range, with the canonical normal virtual bundle. Canonical production of this
chosen model is a library follow-up. -/
abbrev DiagonalSpecializationOfRankLoci (X : SchemeOverField k)
    [Smooth X.hom] :=
  ClosedDeformation X.hom
    ((diagonal X).left.coborderRange.ι ≫ (X ⨯ X).hom)
    (diagonal X).left.liftCoborder
    (factorization_over X.hom (X ⨯ X).hom (diagonal X).left (Over.w (diagonal X))
      (diagonal X).left.liftCoborder (diagonal X).left.coborderRange.ι
      (diagonal X).left.liftCoborder_ι)
    (diagonalVirtualNormalBundleOfRankLoci X).toCoborder

/-- The completed diagonal Gysin class on all clopen rank loci of a smooth scheme. -/
noncomputable def diagonalCompletedClassOfRankLoci (X : SchemeOverField k)
    [Smooth X.hom]
    (D : DiagonalSpecializationOfRankLoci X) :
    CompletedClass (fun _ ↦ (0 : ℤ)) X.hom (X ⨯ X).hom (diagonal X).left
      (Over.w (diagonal X)) (diagonalVirtualNormalBundleOfRankLoci X) :=
  composeClasses (fun _ ↦ (0 : ℤ)) X.hom (X ⨯ X).hom (diagonal X).left
    (Over.w (diagonal X)) (diagonal X).left.liftCoborder
    (diagonal X).left.coborderRange.ι (diagonal X).left.liftCoborder_ι
    (diagonalVirtualNormalBundleOfRankLoci X)
    (closedClass (fun _ ↦ (0 : ℤ)) X.hom
      ((diagonal X).left.coborderRange.ι ≫ (X ⨯ X).hom)
      (diagonal X).left.liftCoborder
      (factorization_over X.hom (X ⨯ X).hom (diagonal X).left (Over.w (diagonal X))
        (diagonal X).left.liftCoborder (diagonal X).left.coborderRange.ι
        (diagonal X).left.liftCoborder_ι)
      (diagonalVirtualNormalBundleOfRankLoci X).toCoborder D)

/-- The global degree-`r` diagonal Gysin coefficient obtained by gluing the completed
class over all clopen rank loci. -/
noncomputable def diagonalGysinClassOfRankLoci (X : SchemeOverField k)
    [Smooth X.hom] (D : DiagonalSpecializationOfRankLoci X) (r : ℕ) :
    BivariantClass (fun _ ↦ 0) (diagonal X) (r : ℤ) :=
  (diagonalGysinClass_overHom X).symm ▸
  ((BivariantClass.OpenRestriction.Completion.globalEquiv (fun _ ↦ (0 : ℤ))
      (overHom X.hom (X ⨯ X).hom (diagonal X).left (Over.w (diagonal X)))
      (fun n : ℕ ↦ @rankOpen X.left (X ⨯ X).left (diagonal X).left
        (diagonal_isImmersion X) (diagonalVirtualNormalBundleOfRankLoci X) n)
      (fun _ : Unit ↦ (⊤ : (X ⨯ X).left.Opens)) (fun _ ↦ Unit.unit)
      (@Scheme.Modules.rankClopen_iSup X.left
        (diagonalVirtualNormalBundleOfRankLoci X).module
        (diagonalVirtualNormalBundleOfRankLoci X).isFiniteLocallyFree)
      (by simp; rfl)
      (@Scheme.Modules.rankClopen_pairwiseDisjoint X.left
        (diagonalVirtualNormalBundleOfRankLoci X).module
        (diagonalVirtualNormalBundleOfRankLoci X).isFiniteLocallyFree)
      (by intro a b h; exact (h (Subsingleton.elim a b)).elim)
      (fun n ↦ (@Scheme.Modules.rankClopen X.left
        (diagonalVirtualNormalBundleOfRankLoci X).module
        (diagonalVirtualNormalBundleOfRankLoci X).isFiniteLocallyFree n).isClopen)
      (fun _ ↦ isClopen_univ)
      (fun n ↦ rankOpen_le_preimage_top X.hom (X ⨯ X).hom (diagonal X).left
        (Over.w (diagonal X)) (diagonalVirtualNormalBundleOfRankLoci X) n))
    (diagonalCompletedClassOfRankLoci X D)).1 r

/-- Restriction of each global diagonal coefficient to a rank locus recovers the
corresponding coefficient of the completed diagonal class. -/
theorem diagonalGysinClassOfRankLoci_component (X : SchemeOverField k)
    [Smooth X.hom] (D : DiagonalSpecializationOfRankLoci X) (n r : ℕ) :
    BivariantClass.ComponentRestriction.restrict (fun _ ↦ (0 : ℤ))
      (overHom X.hom (X ⨯ X).hom (diagonal X).left (Over.w (diagonal X))) (r : ℤ)
      (@rankOpen X.left (X ⨯ X).left (diagonal X).left
        (diagonal_isImmersion X) (diagonalVirtualNormalBundleOfRankLoci X) n) ⊤
      (rankOpen_le_preimage_top X.hom (X ⨯ X).hom (diagonal X).left
        (Over.w (diagonal X)) (diagonalVirtualNormalBundleOfRankLoci X) n)
      ((diagonalGysinClass_overHom X) ▸ diagonalGysinClassOfRankLoci X D r) =
      diagonalCompletedClassOfRankLoci X D n r := sorry

/-- For a diagonal conormal sheaf of constant rank `r`, the rank-locus Gysin family
is concentrated in degree `r` and agrees there with the fixed-rank diagonal class. -/
theorem diagonalGysinClassOfRankLoci_eq_ofRank (X : SchemeOverField k)
    [Smooth X.hom] (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecializationOfRankLoci X) :
    diagonalGysinClassOfRankLoci X D r = diagonalGysinClass X r D ∧
      ∀ n : ℕ, n ≠ r → diagonalGysinClassOfRankLoci X D n =
        BivariantClass.pointwiseZero (fun _ ↦ 0) (diagonal X) (n : ℤ) := sorry

end AlgebraicGeometry.ChowGroup
