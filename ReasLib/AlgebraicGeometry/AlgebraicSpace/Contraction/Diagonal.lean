/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.DiagonalEqualizer
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Solution
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.LocallyNoetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.ComplementInclusion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Slice
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction.Construction

/-!
# Diagonal fibres of contraction triples

Open comparison, the contraction over the test scheme, and representation of
agreement by a solution of that contraction (Stacks, Tag 0GHD).
-/
@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty TopologicalSpace TypeCat
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.Scheme.Over
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

namespace DiagonalEqualizer

variable {σ : ContractionSituation S} {V : Over S}
  [AlgebraicGeometry.IsLocallyNoetherian V.left]

/-- The restriction of `ξ1.u'` to `V \ (Z_1 ∪ Z_2)`. -/
def leftOpen (ξ1 ξ2 : Triple σ V) :
    openComplementAlong (ofOver V) (ξ1.Z ⊔ ξ2.Z) ⟶ σ.openComplement :=
  openComplementAlong.mapOfLe le_sup_left ≫ ξ1.u'

/-- The restriction of `ξ2.u'` to `V \ (Z_1 ∪ Z_2)`. -/
def rightOpen (ξ1 ξ2 : Triple σ V) :
    openComplementAlong (ofOver V) (ξ1.Z ⊔ ξ2.Z) ⟶ σ.openComplement :=
  openComplementAlong.mapOfLe le_sup_right ≫ ξ2.u'

/-- The image of the interpolating equalizer meets the union of the two closed subsets only in their intersection. -/
theorem _root_.AlgebraicGeometry.AlgebraicSpace.ContractionSituation.image_inter_subset (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    Set.range (Points.map (DiagonalEqualizer.of ξ1 ξ2 w1 w2).toV) ∩
        (ξ1.Z ∪ ξ2.Z) ⊆
      (ξ1.Z ⊓ ξ2.Z : Set _) :=
  sorry

/-- The underlying `V`-section of `E' ×_V (V \ Z)` lands in
`V \ (Z_1 ∪ Z_2)`. -/
theorem openRestrict_spec (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx)
    {U : (Over S)ᵒᵖ}
    (x : (openPullback (of ξ1 ξ2 w1 w2)).functorOfPoints.obj U) :
    Set.range
        (Points.map (X := ofOver U.unop) (Y := ofOver V)
          (yonedaEquiv.symm
            ((openPullbackSnd (of ξ1 ξ2 w1 w2)).app U x).1 :
              ofOver U.unop ⟶ ofOver V)) ⊆
      (ξ1.Z ⊔ ξ2.Z : Set (Points (ofOver V)))ᶜ :=
  sorry

/-- The induced morphism `E' ×_V (V \ Z) ⟶ V \ (Z_1 ∪ Z_2)`. -/
def openRestrict (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    openPullback (of ξ1 ξ2 w1 w2) ⟶
      openComplementAlong (ofOver V) (ξ1.Z ⊔ ξ2.Z) where
  app U := ofHom fun x ↦
    ⟨(openPullbackSnd (of ξ1 ξ2 w1 w2)).app U x |>.1,
      openRestrict_spec ξ1 ξ2 w1 w2 x⟩
  naturality := sorry

/-- Postcomposing `openRestrict` with the inclusion of
`V \ (Z_1 ∪ Z_2)` into `V \ Z` recovers the projection to `V \ Z`. -/
theorem openRestrict_comp_mapOfLe (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    openRestrict ξ1 ξ2 w1 w2 ≫
        openComplementAlong.mapOfLe
          (inf_le_sup : ξ1.Z ⊓ ξ2.Z ≤ ξ1.Z ⊔ ξ2.Z) =
      openPullbackSnd (of ξ1 ξ2 w1 w2) :=
  sorry

/-- The algebraic space over `V` whose `T`-points are maps into `E'` over `V`. -/
def sliceSpace (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    AlgebraicSpace V.left :=
  AlgebraicSpace.sliceSpace (of ξ1 ξ2 w1 w2).space (of ξ1 ξ2 w1 w2).toV

/-- `E'` over `V` is locally of finite type. -/
theorem instLocallyOfFiniteType_sliceSpace (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    LocallyOfFiniteType (toBase (sliceSpace ξ1 ξ2 w1 w2)) :=
  sorry

/-- `E'` over `V` is locally Noetherian. -/
theorem instIsLocallyNoetherian_sliceSpace (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    IsLocallyNoetherian (sliceSpace ξ1 ξ2 w1 w2) :=
  sorry

/-- The inverse image `(E' ⟶ V)⁻¹ Z` as a closed subset of `E'` over `V`. -/
def sliceClosed (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    Closeds (Points (sliceSpace ξ1 ξ2 w1 w2)) :=
  ((of ξ1 ξ2 w1 w2).closed.preimage
      (Points.continuous_map (of ξ1 ξ2 w1 w2).toV)).preimage
    (continuous_pointsSlice (of ξ1 ξ2 w1 w2).space (of ξ1 ξ2 w1 w2).toV)

/-- The fibre of `E_W` over `V`. -/
def sliceFormal (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    (Over V.left)ᵒᵖ ⥤ Type u :=
  Scheme.Over.fiberFunctor (toOver (of ξ1 ξ2 w1 w2))
    (yonedaEquiv (𝟙 (ofOver V)))

/-- The fibre of `E_W` over `V` is a formal algebraic space. -/
theorem instIsFormal_sliceFormal (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    FormalAlgebraicSpace.IsFormalAlgebraicSpace (sliceFormal ξ1 ξ2 w1 w2) :=
  sorry

/-- The fibre of `E_W` over `V` is locally Noetherian. -/
theorem instIsLocallyNoetherian_sliceFormal (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    @FormalAlgebraicSpace.IsLocallyNoetherian _ (sliceFormal ξ1 ξ2 w1 w2)
      (instIsFormal_sliceFormal ξ1 ξ2 w1 w2) :=
  sorry

/-- Completing a slice section along `(E' ⟶ V)⁻¹ Z` yields a completion of
`E'` along the inverse image of `Z`. -/
private theorem sliceFactor_mapsInto (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx)
    {U : (Over V.left)ᵒᵖ}
    (x : (completionAlong (sliceSpace ξ1 ξ2 w1 w2)
      (sliceClosed ξ1 ξ2 w1 w2)).obj U) :
    mapsInto
      (((of ξ1 ξ2 w1 w2).closed.preimage
          (Points.continuous_map (of ξ1 ξ2 w1 w2).toV) : Closeds _) : Set _)
      (x.1).1 :=
  sorry

/-- The image of `sliceFactor` in `E_W` lies over the structure morphism of
`T`. -/
private theorem sliceFactor_liesOver (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx)
    {U : (Over V.left)ᵒᵖ}
    (x : (completionAlong (sliceSpace ξ1 ξ2 w1 w2)
      (sliceClosed ξ1 ξ2 w1 w2)).obj U) :
    (toOver (of ξ1 ξ2 w1 w2)).app (op ((Over.map V.hom).obj U.unop))
        ((of ξ1 ξ2 w1 w2).factor.app (op ((Over.map V.hom).obj U.unop))
          ⟨(x.1).1, sliceFactor_mapsInto ξ1 ξ2 w1 w2 x⟩) =
      yonedaEquiv (ofOverMap (Scheme.Over.fromOver U.unop)) :=
  sorry

/-- The restriction of `E'_{/Z} ⟶ E_W` to schemes over `V`. -/
def sliceFactor (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    completionAlong (sliceSpace ξ1 ξ2 w1 w2) (sliceClosed ξ1 ξ2 w1 w2) ⟶
      sliceFormal ξ1 ξ2 w1 w2 where
  app U := ofHom fun x ↦
    ⟨(of ξ1 ξ2 w1 w2).factor.app (op ((Over.map V.hom).obj U.unop))
        ⟨(x.1).1, by exact sliceFactor_mapsInto ξ1 ξ2 w1 w2 x⟩,
      by exact sliceFactor_liesOver ξ1 ξ2 w1 w2 x⟩
  naturality := sorry

/-- The reduction of the fibre of `E_W` is locally of finite type over `V`. -/
theorem instLocallyOfFiniteType_sliceReduction (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    LocallyOfFiniteType
      (toBase (@FormalAlgebraicSpace.reductionSpace V.left (sliceFormal ξ1 ξ2 w1 w2)
        (instIsFormal_sliceFormal ξ1 ξ2 w1 w2)
        (instIsLocallyNoetherian_sliceFormal ξ1 ξ2 w1 w2))) :=
  sorry

/-- The comparison over `V` is locally of finite type. -/
theorem instLocallyOfFiniteType_sliceFactor (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    FormalAlgebraicSpace.LocallyOfFiniteType (sliceFactor ξ1 ξ2 w1 w2) :=
  sorry

/-- The comparison over `V` is a formal modification. -/
theorem instFormalModification_sliceFactor (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    @FormalAlgebraicSpace.FormalModification V.left
      (completionAlong (sliceSpace ξ1 ξ2 w1 w2) (sliceClosed ξ1 ξ2 w1 w2)) (sliceFormal ξ1 ξ2 w1 w2)
      (sliceFactor ξ1 ξ2 w1 w2)
      (instIsFormalAlgebraicSpace_completionAlong (sliceSpace ξ1 ξ2 w1 w2) (sliceClosed ξ1 ξ2 w1 w2))
      (instIsFormal_sliceFormal ξ1 ξ2 w1 w2)
      (@instIsLocallyNoetherian_completionAlong V.left (sliceSpace ξ1 ξ2 w1 w2)
        (instIsLocallyNoetherian_sliceSpace ξ1 ξ2 w1 w2) (sliceClosed ξ1 ξ2 w1 w2))
      (instIsLocallyNoetherian_sliceFormal ξ1 ξ2 w1 w2) (instLocallyOfFiniteType_sliceFactor ξ1 ξ2 w1 w2) :=
  sorry

/-- The contraction situation over `V` with algebraic space `E'` over `V`,
closed subset `(E' ⟶ V)⁻¹ Z`, formal algebraic space the fibre of `E_W`, and
comparison the restriction of `factor`. -/
def toSituation (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    ContractionSituation V.left where
  X' := sliceSpace ξ1 ξ2 w1 w2
  locallyOfFiniteType_X' := instLocallyOfFiniteType_sliceSpace ξ1 ξ2 w1 w2
  isLocallyNoetherian_X' := instIsLocallyNoetherian_sliceSpace ξ1 ξ2 w1 w2
  T' := sliceClosed ξ1 ξ2 w1 w2
  W := sliceFormal ξ1 ξ2 w1 w2
  isFormal_W := instIsFormal_sliceFormal ξ1 ξ2 w1 w2
  isLocallyNoetherian_W := instIsLocallyNoetherian_sliceFormal ξ1 ξ2 w1 w2
  reductionData_W := @FormalAlgebraicSpace.reductionData V.left
    (sliceFormal ξ1 ξ2 w1 w2) (instIsFormal_sliceFormal ξ1 ξ2 w1 w2)
    (instIsLocallyNoetherian_sliceFormal ξ1 ξ2 w1 w2)
  locallyOfFiniteType_red := instLocallyOfFiniteType_sliceReduction ξ1 ξ2 w1 w2
  g := sliceFactor ξ1 ξ2 w1 w2
  locallyOfFiniteType_g := instLocallyOfFiniteType_sliceFactor ξ1 ξ2 w1 w2
  isFormalModification := instFormalModification_sliceFactor ξ1 ξ2 w1 w2

/-- The algebraic space of `toSituation` is `E'` viewed over `V`. -/
theorem toSituation_X' (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    (toSituation ξ1 ξ2 w1 w2).X' = sliceSpace ξ1 ξ2 w1 w2 :=
  rfl

/-- The closed subset of `toSituation` is `(E' ⟶ V)⁻¹ Z`. -/
theorem toSituation_T' (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    (toSituation ξ1 ξ2 w1 w2).T' = sliceClosed ξ1 ξ2 w1 w2 :=
  rfl

/-- The formal algebraic space of `toSituation` is the fibre of `E_W` over
`V`. -/
theorem toSituation_W (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    (toSituation ξ1 ξ2 w1 w2).W = sliceFormal ξ1 ξ2 w1 w2 :=
  rfl

/-- The comparison of `toSituation` is the restriction of `factor`. -/
theorem toSituation_g (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    (toSituation ξ1 ξ2 w1 w2).g = sliceFactor ξ1 ξ2 w1 w2 :=
  rfl

/-- The two triples restrict to the same element of `F(A)` along `φ : A ⟶ V`. -/
def agrees (ξ1 ξ2 : Triple σ V) {A : Over S}
    [locallyNoetherian_A : AlgebraicGeometry.IsLocallyNoetherian A.left] (φ : A ⟶ V) : Prop :=
  Triple.map φ ξ1 = Triple.map φ ξ2

/-- Agreement of the two triples is stable under precomposition over `V`. -/
theorem agrees_restrict (ξ1 ξ2 : Triple σ V) {A B : Over V.left}
    [AlgebraicGeometry.IsLocallyNoetherian A.left]
    [AlgebraicGeometry.IsLocallyNoetherian B.left]
    (φ : B ⟶ A) (h : agrees ξ1 ξ2 (locallyNoetherian_A := ‹AlgebraicGeometry.IsLocallyNoetherian A.left›)
      (Scheme.Over.fromOver A)) :
    agrees ξ1 ξ2 (locallyNoetherian_A := ‹AlgebraicGeometry.IsLocallyNoetherian B.left›)
      (Scheme.Over.fromOver B) :=
  sorry

/-- The functor on locally Noetherian schemes over `V` sending `φ` to the
proposition `Triple.map φ ξ1 = Triple.map φ ξ2`. -/
def agreesFunctor (ξ1 ξ2 : Triple σ V) :
    (locallyNoetherian V.left).FullSubcategoryᵒᵖ ⥤ Type (u + 1) where
  obj A := ULift.{u + 1} (PLift (agrees ξ1 ξ2 (A := (Over.map V.hom).obj A.unop.obj)
      (locallyNoetherian_A := A.unop.property)
      (Scheme.Over.fromOver A.unop.obj)))
  map φ := ofHom fun x ↦
    ⟨⟨agrees_restrict ξ1 ξ2 φ.unop.hom x.down.down⟩⟩
  map_id := sorry
  map_comp := sorry

/-- Components of `agreesFunctor` are `PLift` of agreement of the restricted
triples. -/
theorem agreesFunctor_obj (ξ1 ξ2 : Triple σ V)
    (A : (locallyNoetherian V.left).FullSubcategory) :
    (agreesFunctor ξ1 ξ2).obj (op A) =
      ULift.{u + 1} (PLift (agrees ξ1 ξ2 (A := (Over.map V.hom).obj A.obj)
      (locallyNoetherian_A := A.property)
      (Scheme.Over.fromOver A.obj))) :=
  rfl

end DiagonalEqualizer

variable {σ : ContractionSituation S} {V : Over S}
  [AlgebraicGeometry.IsLocallyNoetherian V.left]
variable (ξ1 ξ2 : Triple σ V)
variable (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
variable (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx)

/-- The open restriction of the interpolating equalizer is a monomorphism and equalizes the two open maps universally. -/
theorem openRestrict_mono :
    Mono (DiagonalEqualizer.openPullbackSnd (DiagonalEqualizer.of ξ1 ξ2 w1 w2)) ∧
      DiagonalEqualizer.openRestrict ξ1 ξ2 w1 w2 ≫
          openComplementAlong.mapOfLe
            (inf_le_sup : ξ1.Z ⊓ ξ2.Z ≤ ξ1.Z ⊔ ξ2.Z) =
        DiagonalEqualizer.openPullbackSnd
          (DiagonalEqualizer.of ξ1 ξ2 w1 w2) ∧
      IsPullback
        (DiagonalEqualizer.openRestrict ξ1 ξ2 w1 w2 ≫
          DiagonalEqualizer.leftOpen ξ1 ξ2)
        (DiagonalEqualizer.openRestrict ξ1 ξ2 w1 w2)
        (prod.lift (𝟙 σ.openComplement) (𝟙 σ.openComplement))
        (prod.lift (DiagonalEqualizer.leftOpen ξ1 ξ2)
          (DiagonalEqualizer.rightOpen ξ1 ξ2)) :=
  sorry

/-- Two compatible triples agree after restriction if and only if their open and completed structure maps factor through the corresponding equalizers. -/
theorem restricts_iff_factors {A : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian A.left] (φ : A ⟶ V) :
    DiagonalEqualizer.agrees ξ1 ξ2 φ ↔
      (∃ h : openComplementAlong (ofOver A)
            ((DiagonalEqualizer.of ξ1 ξ2 w1 w2).closed.preimage
              (Points.continuous_map (ofOverMap φ))) ⟶
          DiagonalEqualizer.openPullback (DiagonalEqualizer.of ξ1 ξ2 w1 w2),
        h ≫ DiagonalEqualizer.openPullbackSnd
            (DiagonalEqualizer.of ξ1 ξ2 w1 w2) =
          openComplementAlong.map (ofOverMap φ)
            (DiagonalEqualizer.of ξ1 ξ2 w1 w2).closed) ∧
      (∃ k : completionAlong (ofOver A)
            ((DiagonalEqualizer.of ξ1 ξ2 w1 w2).closed.preimage
              (Points.continuous_map (ofOverMap φ))) ⟶
          (DiagonalEqualizer.of ξ1 ξ2 w1 w2).formal,
        k ≫ (DiagonalEqualizer.of ξ1 ξ2 w1 w2).toFormal =
          completionAlong.map (ofOverMap φ)
            (DiagonalEqualizer.of ξ1 ξ2 w1 w2).closed) :=
  sorry

/-- A morphism into a solution over `V` forces the two triples to agree. -/
theorem agrees_of_solutionHom (E : AlgebraicSpace V.left)
    [LocallyOfFiniteType (toBase E)]
    (sol : SolutionFor (DiagonalEqualizer.toSituation ξ1 ξ2 w1 w2) E)
    {A : (locallyNoetherian V.left).FullSubcategory}
    (f : ofOver A.obj ⟶ E) :
    DiagonalEqualizer.agrees ξ1 ξ2 (A := (Over.map V.hom).obj A.obj)
      (locallyNoetherian_A := A.property)
      (Scheme.Over.fromOver A.obj) :=
  sorry

/-- The comparison from morphisms into a solution to agreement of the two
triples, on locally Noetherian schemes over `V`. -/
def diagonalFiberHom (E : AlgebraicSpace V.left)
    [LocallyOfFiniteType (toBase E)]
    (sol : SolutionFor (DiagonalEqualizer.toSituation ξ1 ξ2 w1 w2) E) :
    homOnLocallyNoetherian E ⟶ DiagonalEqualizer.agreesFunctor ξ1 ξ2 where
  app A := ofHom fun f ↦ ⟨⟨agrees_of_solutionHom ξ1 ξ2 w1 w2 E sol f⟩⟩
  naturality := sorry

/-- A solution of the equalizer contraction situation represents the diagonal fiber of the contraction functor on locally Noetherian schemes. -/
@[stacks 0GHD]
theorem represents_diagonalFiber (E : AlgebraicSpace V.left)
    [LocallyOfFiniteType (toBase E)]
    (sol : SolutionFor (DiagonalEqualizer.toSituation ξ1 ξ2 w1 w2) E) :
    IsIso (diagonalFiberHom ξ1 ξ2 w1 w2 E sol) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
