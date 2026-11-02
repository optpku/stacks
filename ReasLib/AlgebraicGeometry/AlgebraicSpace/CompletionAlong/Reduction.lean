/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.Structure
public import ReasLib.AlgebraicGeometry.Presheaf.Reduction
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening

/-!
# Reduction of completion along a closed subset

The reduction of the completion of an algebraic space along a closed subset is
the reduced induced closed subspace, compatibly with the maps into the ambient space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits
open Opposite TopologicalSpace TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The image on points is detected by the images of scheme-valued sections. -/
private theorem range_map_subset_of_mapsInto {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y.functorOfPoints ⟶ X.functorOfPoints)
    (T : Set (Points X))
    (hf : ∀ (U : Over S) (x : Y.functorOfPoints.obj (op U)),
      mapsInto T (f.app (op U) x)) :
    Set.range (Points.map (X := Y) (Y := X) f) ⊆ T := by
  rintro _ ⟨p, rfl⟩
  induction p using Quotient.inductionOn with
  | h p =>
    let q : FieldValuedPoint (ofOver p.overObj) :=
      FieldValuedPoint.of p.K p.structureHom (𝟙 _)
    apply hf p.overObj (yonedaEquiv p.hom)
    refine ⟨(ofOver.pointsEquiv p.overObj).symm (Points.mk q), ?_⟩
    change Points.map
      (yonedaEquiv.symm (f.app (op p.overObj) (yonedaEquiv p.hom)))
      ((ofOver.pointsEquiv p.overObj)
        ((ofOver.pointsEquiv p.overObj).symm (Points.mk q))) =
      Points.map f (Points.mk p)
    rw [← yonedaEquiv_comp, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    rfl

/-- Sections of the reduced induced closed subspace on `T` map into `T`. -/
theorem mapsInto_reducedι {S : Scheme.{u}} {X : AlgebraicSpace S}
    (T : Closeds (Points X)) {U : (Over S)ᵒᵖ}
    (x : (ReducedClosed.Space.space X T).functorOfPoints.obj U) :
    mapsInto (T : Set (Points X)) ((ReducedClosed.Space.ι X T).app U x) := by
  have hT : Set.range (Points.map (ReducedClosed.Space.ι X T)) =
      (T : Set (Points X)) :=
    ReducedClosed.Immersion.pointsSet_eq X T
  change Set.range (Points.mapOfOver
    (yonedaEquiv.symm ((ReducedClosed.Space.ι X T).app U x))) ⊆ _
  rintro _ ⟨p, rfl⟩
  rw [Points.mapOfOver,
    ← yonedaEquiv_symm_naturality_right U.unop (ReducedClosed.Space.ι X T) x]
  exact hT ▸ ⟨_, (Points.map_comp
    (yonedaEquiv.symm x : ofOver U.unop ⟶ ReducedClosed.Space.space X T)
    (ReducedClosed.Space.ι X T) ((ofOver.pointsEquiv U.unop) p)).symm⟩

namespace completionAlong

/-- The canonical morphism from the reduced induced closed subspace on `T`
into the completion along `T`. -/
def reducedι {S : Scheme.{u}} {X : AlgebraicSpace S} (T : Closeds (Points X)) :
    (ReducedClosed.Space.space X T).functorOfPoints ⟶
      completionAlong X T where
  app U :=
    ofHom fun x ↦
      ⟨(ReducedClosed.Space.ι X T).app U x, mapsInto_reducedι T x⟩
  naturality := by
    intro U V φ
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact congrArg (fun k :
      (ReducedClosed.Space.space X T).functorOfPoints.obj U ⟶
        X.functorOfPoints.obj V ↦ k x)
      ((ReducedClosed.Space.ι X T).naturality φ)

/-- The canonical morphism from the reduced closed subspace to the completion
commutes with the inclusions into the ambient algebraic space. -/
theorem fromReduced_comp_ι {S : Scheme.{u}} {X : AlgebraicSpace S}
    (T : Closeds (Points X)) :
    reducedι T ≫ ι X T = ReducedClosed.Space.ι X T := by
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- The inclusion of the completion is injective on sections. -/
private theorem ι_mono {S : Scheme.{u}} {X : AlgebraicSpace S}
    (T : Closeds (Points X)) : Mono (ι X T) := by
  constructor
  intro F a b h
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  exact congrArg (fun k : F ⟶ X.functorOfPoints ↦ k.app U x) h

/-- Represented scheme properties cancel through a monomorphism of presheaves. -/
private theorem presheaf_of_comp_mono {S : Scheme.{u}}
    {F G H : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H) [Mono b]
    (P : MorphismProperty (Over S)) (ha : P.presheaf (a ≫ b)) :
    P.presheaf a := by
  constructor
  · intro U ξ
    obtain ⟨V, p, q, hp⟩ := ha.rep (ξ ≫ b)
    exact ⟨V, p, q, IsPullback.of_isLimit
      (PullbackCone.isLimitOfFactors (a ≫ b) (ξ ≫ b) b a ξ
        rfl rfl hp.cone hp.isLimit)⟩
  · intro U V ξ p q hp
    exact ha.property (ξ ≫ b) p q (IsPullback.of_isLimit
      (PullbackCone.isLimitOfCompMono a ξ b hp.cone hp.isLimit))

/-- The reduced inclusion remains a represented closed immersion into the completion. -/
private theorem reducedι_closed {S : Scheme.{u}} {X : AlgebraicSpace S}
    (T : Closeds (Points X)) :
    (MorphismProperty.over (@AlgebraicGeometry.IsClosedImmersion)).presheaf
      (reducedι T) := by
  letI := ι_mono T
  apply presheaf_of_comp_mono (reducedι T) (ι X T)
  rw [fromReduced_comp_ι (X := X) T]
  exact ReducedClosed.Immersion.inclusion_closed X T

/-- The canonical morphism from the reduced closed subspace to the completion
is representable by algebraic spaces. -/
theorem fromReduced_representable {S : Scheme.{u}} {X : AlgebraicSpace S}
    (T : Closeds (Points X)) :
    representableByAlgebraicSpaces (reducedι T) := by
  intro U ξ
  exact IsAlgebraicSpace.of_iso ((reducedι_closed T).rep.isPullback ξ).flip.isoPullback.symm

/-- Every Yoneda pullback of the canonical morphism from the reduced closed
subspace to the completion is a thickening. -/
theorem fromReduced_isThickening {S : Scheme.{u}} {X : AlgebraicSpace S}
    (T : Closeds (Points X))
    (ha : representableByAlgebraicSpaces (reducedι T))
    {U : Over S} (ξ : yoneda.obj U ⟶ completionAlong X T) :
    IsThickening (representableByAlgebraicSpaces.pullbackHom ha ξ) := by
  letI := ι_mono T
  refine { toIsClosedImmersion := ⟨?_⟩, toSurjective := ⟨?_⟩ }
  · change (MorphismProperty.over (@AlgebraicGeometry.IsClosedImmersion)).presheaf
      (pullback.fst ξ (reducedι T))
    exact (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.over (@AlgebraicGeometry.IsClosedImmersion))).of_isPullback
        (IsPullback.of_hasPullback ξ (reducedι T)).flip (reducedι_closed T)
  · intro p
    induction p using Quotient.inductionOn with
    | h p =>
      haveI : AlgebraicGeometry.IsReduced p.overObj.left := by
        change AlgebraicGeometry.IsReduced (Spec (CommRingCat.of p.K))
        infer_instance
      let g : yoneda.obj p.overObj ⟶ completionAlong X T := NatTrans.vcomp p.hom ξ
      let f : ofOver p.overObj ⟶ X := NatTrans.vcomp g (ι X T)
      have hT : Set.range (Points.map (ReducedClosed.Space.ι X T)) =
          (T : Set (Points X)) :=
        ReducedClosed.Immersion.pointsSet_eq X T
      have himage : Set.range (Points.map f) ⊆
          Set.range (Points.map (ReducedClosed.Space.ι X T)) := by
        rw [hT]
        exact range_map_subset_of_mapsInto (Y := ofOver p.overObj) (X := X)
          f (T : Set (Points X)) (fun V x ↦ (g.app (op V) x).2)
      obtain ⟨h, hh⟩ :=
        (IsClosedImmersion.exists_lift_iff_range_subset (ReducedClosed.Space.ι X T) f).2
          himage
      have hcomm : NatTrans.vcomp p.hom ξ = NatTrans.vcomp h (reducedι T) := by
        apply (cancel_mono (ι X T)).1
        change g ≫ ι X T = NatTrans.vcomp h (reducedι T ≫ ι X T)
        rw [fromReduced_comp_ι (X := X) T]
        exact hh.symm
      let k : yoneda.obj p.overObj ⟶ pullback ξ (reducedι T) :=
        pullback.lift p.hom h hcomm
      refine ⟨Points.mk (FieldValuedPoint.of p.K p.structureHom k), ?_⟩
      change Points.mk (FieldValuedPoint.of p.K p.structureHom
        (NatTrans.vcomp k (pullback.fst ξ (reducedι T)))) = Points.mk p
      exact congrArg (fun l : yoneda.obj p.overObj ⟶ yoneda.obj U ↦
        Points.mk (FieldValuedPoint.of p.K p.structureHom l : FieldValuedPoint (ofOver U)))
          (pullback.lift_fst (C := (Over S)ᵒᵖ ⥤ Type u)
            (f := ξ) (g := reducedι T) p.hom h hcomm)

/-- A morphism from a reduced algebraic space to the completion factors uniquely
through the reduced induced closed subspace. -/
theorem fromReduced_liftUnique {S : Scheme.{u}} {X : AlgebraicSpace S}
    (T : Closeds (Points X)) {U : AlgebraicSpace S}
    (hU : hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) U)
    (g : U.functorOfPoints ⟶ completionAlong X T) :
    ∃! h : U.functorOfPoints ⟶ (ReducedClosed.Space.space X T).functorOfPoints,
      h ≫ reducedι T = g := by
  letI : AlgebraicSpace.IsReduced U := ⟨hU⟩
  let f : U ⟶ X := NatTrans.vcomp g (ι X T)
  have hT : Set.range (Points.map (ReducedClosed.Space.ι X T)) =
      (T : Set (Points X)) :=
    ReducedClosed.Immersion.pointsSet_eq X T
  have himage : Set.range (Points.map f) ⊆
      Set.range (Points.map (ReducedClosed.Space.ι X T)) := by
    rw [hT]
    exact range_map_subset_of_mapsInto
      (g ≫ ι X T : U.functorOfPoints ⟶ X.functorOfPoints) (T : Set (Points X))
      (fun V x ↦ (g.app (op V) x).2)
  obtain ⟨h, hh, hu⟩ :=
    (IsClosedImmersion.existsUnique_lift_iff_range_subset
      (ReducedClosed.Space.ι X T) f).2 himage
  refine ⟨h, ?_, ?_⟩
  · apply NatTrans.ext
    funext V
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact congrArg (fun k : U ⟶ X ↦ k.app V x) hh
  · intro h' hh'
    apply hu h'
    change h' ≫ (ReducedClosed.Space.ι X T :
      (ReducedClosed.Space.space X T).functorOfPoints ⟶ X.functorOfPoints) = g ≫ ι X T
    rw [← fromReduced_comp_ι (X := X) T, ← Category.assoc, hh']

end completionAlong

/-- Sheafification preserves an inclusion after taking the image along a map. -/
private theorem image_sheafify_le {S : Scheme.{u}}
    (J : GrothendieckTopology (Over S))
    {F G : (Over S)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) (A : Subfunctor F) (B : Subfunctor G)
    (hA : A.image a ≤ B) (hG : Presieve.IsSheaf J G)
    (hB : Presieve.IsSheaf J B.toFunctor) :
    (A.sheafify J).image a ≤ B := by
  rintro U _ ⟨x, hx, rfl⟩
  have hs : a.app U x ∈ ((A.image a).sheafify J).obj U := by
    apply J.superset_covering ?_ hx
    intro V i hi
    exact ⟨F.map i.op x, hi, a.naturality_apply i.op x⟩
  exact ((A.image a).sheafify_le B hA hG hB) U hs

/-- The image of the reduction of the completion along `T` in the ambient
algebraic space is the reduced induced closed subspace on `T`. -/
theorem reduction_completionAlong {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Closeds (Points X)) :
    (SpacePresheaf.reduction (completionAlong X T)).image (completionAlong.ι X T) =
      Subfunctor.range (ClosedSubspaceStructure.reduced T).ι :=
  by
  let J := Scheme.fppfTopology.over S
  let A := SpacePresheaf.reducedGenerators (completionAlong X T)
  let B := (Subfunctor.range (ReducedClosed.AtlasImage.chartMap X T)).sheafify J
  change (A.sheafify J).image (completionAlong.ι X T) = Subfunctor.range B.ι
  rw [Subfunctor.range_ι]
  apply le_antisymm
  · have hX : Presieve.IsSheaf J X.functorOfPoints :=
      (isSheaf_iff_isSheaf_of_type _ _).mp X.isSheaf
    apply image_sheafify_le J (completionAlong.ι X T) A B ?_ hX
      ((Subfunctor.range (ReducedClosed.AtlasImage.chartMap X T)).sheafify_isSheaf hX)
    change (⨆ (V : Over S) (_ : AlgebraicGeometry.IsReduced V.left)
      (g : yoneda.obj V ⟶ completionAlong X T), Subfunctor.range g).image
        (completionAlong.ι X T) ≤ B
    apply (Subfunctor.image_le_iff _ (completionAlong.ι X T) B).2
    refine iSup_le fun V ↦ iSup_le fun hV ↦ iSup_le fun g ↦ ?_
    obtain ⟨h, hh, _⟩ := completionAlong.fromReduced_liftUnique T (U := ofOver V)
      ⟨V, 𝟙 _, ofOver_id_presheaf_etale V, ofOver_id_locallySurjective V, hV⟩ g
    change Subfunctor.range g ≤ B.preimage (completionAlong.ι X T)
    have hc : g ≫ completionAlong.ι X T =
        NatTrans.vcomp h (ReducedClosed.Space.ι X T) := by
      rw [← hh]
      change (h ≫ completionAlong.reducedι T) ≫ completionAlong.ι X T =
        h ≫ (ReducedClosed.Space.ι X T)
      rw [Category.assoc, completionAlong.fromReduced_comp_ι (X := X) T]
    intro W x hx
    obtain ⟨z, rfl⟩ := hx
    change (completionAlong.ι X T).app W (g.app W z) ∈ B.obj W
    rw [show (completionAlong.ι X T).app W (g.app W z) =
      (ReducedClosed.Space.ι X T).app W (h.app W z) from
      congrArg (fun k : yoneda.obj V ⟶ X.functorOfPoints ↦ k.app W z) hc]
    exact (h.app W z).property
  · let c : yoneda.obj (ReducedClosed.AtlasImage.reducedAtlas X T) ⟶ completionAlong X T :=
      NatTrans.vcomp (ReducedClosed.Space.chart X T) (completionAlong.reducedι T)
    have hgen : Subfunctor.range c ≤ A :=
      le_iSup_of_le (ReducedClosed.AtlasImage.reducedAtlas X T)
        (le_iSup_of_le (ReducedClosed.Space.reducedAtlas_reduced X T)
          (le_iSup_of_le c le_rfl))
    have hc : c ≫ completionAlong.ι X T = ReducedClosed.AtlasImage.chartMap X T := by
      change NatTrans.vcomp (ReducedClosed.Space.chart X T)
        (completionAlong.reducedι T ≫ completionAlong.ι X T) = _
      rw [completionAlong.fromReduced_comp_ι (X := X) T]
      exact ReducedClosed.Space.chart_ι X T
    intro U x hx
    let z : (ReducedClosed.Space.space X T).functorOfPoints.obj U := ⟨x, hx⟩
    refine ⟨(completionAlong.reducedι T).app U z, ?_, rfl⟩
    apply J.superset_covering ?_ hx
    intro V i hi
    obtain ⟨v, hv⟩ := hi
    apply hgen (op V)
    refine ⟨v, ?_⟩
    apply Subtype.ext
    change (completionAlong.ι X T).app (op V) (c.app (op V) v) =
      X.functorOfPoints.map i.op x
    exact (congrArg (fun k : yoneda.obj (ReducedClosed.AtlasImage.reducedAtlas X T) ⟶
      X.functorOfPoints ↦ k.app (op V) v) hc).trans hv

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- The completion of an algebraic space along a closed subset is a formal
algebraic space. -/
instance instIsFormalAlgebraicSpace_completionAlong {S : Scheme.{u}}
    (X : AlgebraicSpace S) (T : Closeds (Points X)) :
    IsFormalAlgebraicSpace (AlgebraicSpace.completionAlong X T) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
