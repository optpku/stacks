module

public import ReasLib.AlgebraicGeometry.BivariantClass.Restriction
public import ReasLib.AlgebraicGeometry.ChowGroup.ExteriorProduct
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import ReasLib.AlgebraicGeometry.Scheme.Module.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive
public import stacks_project.Chap42.Lemma_42_55_3_NormalClass
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-!
# Intersection products of Chow classes over a field

This file packages the section 42.62 product `α · β = Δ!(α × β)` as the identity-square
cap of the Chow exterior product by the canonical degree-`dim X` Gysin class of the
diagonal, together with the Chow classes of closed subschemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed
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

/-- Dualizing reverses an isomorphism of module sheaves. -/
noncomputable def dualMapIso {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G) :
    Scheme.Modules.dual G ≅ Scheme.Modules.dual F where
  hom := dualMap e.hom
  inv := dualMap e.inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Dualizing an isomorphism uses `dualMap` on the forward arrow. -/
theorem dualMapIso_hom {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G) :
    (dualMapIso e).hom = dualMap e.hom := sorry

/-- The normal sheaf of a morphism is the internal Hom of the conormal sheaf into the
structure sheaf, identified with the dual of the conormal sheaf. -/
noncomputable def normalSheafIsoDualConormal {Z X : Scheme.{u}} (i : Z ⟶ X) :
    normalSheaf i ≅ Scheme.Modules.dual (conormalSheaf i) :=
  (ihom (conormalSheaf i)).mapIso (RingedSpace.unitIsoTensorUnit Z.toRingedSpace)

/-- `normalSheafIsoDualConormal` is internal Hom applied to the tensor-unit comparison. -/
theorem normalSheafIsoDualConormal_hom {Z X : Scheme.{u}} (i : Z ⟶ X) :
    (normalSheafIsoDualConormal i).hom =
      (ihom (conormalSheaf i)).map
        (RingedSpace.unitIsoTensorUnit Z.toRingedSpace).hom := sorry

/-- The canonical evaluation morphism from the conormal sheaf to the dual of the normal
sheaf. -/
noncomputable def biduality {Z X : Scheme.{u}} (i : Z ⟶ X) :
    conormalSheaf i ⟶ Scheme.Modules.dual (normalSheaf i) :=
  toReflexiveHull (conormalSheaf i) ≫
    (dualMapIso (normalSheafIsoDualConormal i)).hom

/-- Finite locally free conormal sheaves are reflexive, so `biduality` is an isomorphism. -/
theorem biduality_isIso {Z X : Scheme.{u}} (i : Z ⟶ X) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf i)] :
    IsIso (biduality i) := sorry

/-- The canonical biduality identification `dual (normalSheaf i) ≅ conormalSheaf i`. -/
noncomputable def bidualityIso {Z X : Scheme.{u}} (i : Z ⟶ X) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf i)] :
    Scheme.Modules.dual (normalSheaf i) ≅ conormalSheaf i :=
  (@asIso _ _ _ _ (biduality i) (biduality_isIso i r)).symm

/-- The inverse of `bidualityIso` is the canonical evaluation morphism. -/
theorem bidualityIso_inv {Z X : Scheme.{u}} (i : Z ⟶ X) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf i)] :
    (bidualityIso i r).inv = biduality i := sorry

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
    (diagonalVirtualNormalBundle X r).module = normalSheaf (diagonal X).left := sorry

/-- Closed-specialization data for the coborder factorization of the Over-diagonal. -/
abbrev DiagonalSpecialization (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)] :=
  ClosedSpecialization (fun _ ↦ (0 : ℤ)) X.hom
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
      IsOpenImmersion (diagonal X).left.coborderRange.ι := sorry

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
          (diagonalVirtualNormalBundle X r).toCoborder D) := sorry

/-- The Over-hom used by `diagonalGysinClass` is the categorical diagonal. -/
theorem diagonalGysinClass_overHom (X : SchemeOverField k) :
    overHom X.hom (X ⨯ X).hom (diagonal X).left (Over.w (diagonal X)) =
      diagonal X := sorry

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
      (ClosedSpecialization.rankOpen_iSup (diagonal X).left
        (diagonalVirtualNormalBundle X r))
      (ClosedSpecialization.unitTop_iSup (X ⨯ X).left)
      (ClosedSpecialization.rankOpen_pairwiseDisjoint (diagonal X).left
        (diagonalVirtualNormalBundle X r))
      (ClosedSpecialization.unitTop_pairwiseDisjoint (X ⨯ X).left)
      (ClosedSpecialization.rankOpen_isClopen (diagonal X).left
        (diagonalVirtualNormalBundle X r))
      (ClosedSpecialization.unitTop_isClopen (X ⨯ X).left)
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
        (exteriorProductPairing X X n m alpha beta) := sorry

/-- The Chow class of a closed subscheme in a fixed relative dimension. -/
noncomputable def closedSubschemeClass (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] (Y : X.left.IdealSheafData) (n : ℤ)
    (hY : X.hom.closedSubschemeDeltaDimension (fun _ ↦ 0) Y ≤ (n : EInt)) :
    RelativeChow (fun _ ↦ 0) X n :=
  @chowClass X.left
    (@LocallyOfFiniteType.isLocallyNoetherian X.left (Spec (CommRingCat.of k)) X.hom
      inferInstance
      (@instUniversallyCatenarySpec k inferInstance
        instUniversallyCatenaryRingOfField.{u, u}).toIsLocallyNoetherian)
    (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n
    (@Scheme.Hom.closedSubschemeCycle X.left (Spec (CommRingCat.of k)) X.hom
      (@instUniversallyCatenarySpec k inferInstance
        instUniversallyCatenaryRingOfField.{u, u})
      inferInstance (fun _ ↦ 0) inferInstance Y n hY)

/-- The closed-subscheme class is the Chow class of the associated closed-subscheme cycle. -/
theorem closedSubschemeClass_def (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] (Y : X.left.IdealSheafData) (n : ℤ)
    (hY : X.hom.closedSubschemeDeltaDimension (fun _ ↦ 0) Y ≤ (n : EInt)) :
    closedSubschemeClass X Y n hY =
      @chowClass X.left
        (@LocallyOfFiniteType.isLocallyNoetherian X.left (Spec (CommRingCat.of k))
          X.hom inferInstance
          (@instUniversallyCatenarySpec k inferInstance
            instUniversallyCatenaryRingOfField.{u, u}).toIsLocallyNoetherian)
        (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n
        (@Scheme.Hom.closedSubschemeCycle X.left (Spec (CommRingCat.of k)) X.hom
          (@instUniversallyCatenarySpec k inferInstance
            instUniversallyCatenaryRingOfField.{u, u})
          inferInstance (fun _ ↦ 0) inferInstance Y n hY) := sorry

end AlgebraicGeometry.ChowGroup
