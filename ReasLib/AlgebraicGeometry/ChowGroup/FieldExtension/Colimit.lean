module

public import ReasLib.AlgebraicGeometry.ChowGroup.FlatBaseChange.Composition
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.FiniteIntermediate
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Chow groups over finite intermediate fields

This module constructs Chow groups after base change to finite-dimensional intermediate
fields of a field extension, the transition and limit-leg morphisms of that inverse system,
and the filtered-colimit universal property of the Chow group after base change to the full
extension.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.FieldExtension

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.FieldExtension

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
variable (X : Over (Spec (CommRingCat.of k))) [Scheme.Hom.FiniteType X.hom]
variable (i : ℤ)

/-- The base change of a scheme to a finite intermediate field. -/
noncomputable abbrev finiteIntermediateBaseChange
    (L : FiniteIntermediateField k K) : Over (finiteIntermediateSpec k K L) :=
  (Over.pullback (finiteIntermediateStructureMap k K L)).obj X

/-- The Chow group of the base change to a finite intermediate field. -/
abbrev finiteIntermediateObject (L : FiniteIntermediateField k K) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of
    (@ChowGroup.{u} (finiteIntermediateBaseChange k K X L).left
      (@LocallyOfFiniteType.isLocallyNoetherian
        (finiteIntermediateBaseChange k K X L).left
        (finiteIntermediateSpec k K L)
        (finiteIntermediateBaseChange k K X L).hom inferInstance
        (finiteIntermediateDiagram_universallyCatenary k K
          (OrderDual.toDual L)).toIsLocallyNoetherian)
      ((finiteIntermediateBaseChange k K X L).hom.relativeDimensionFunction
        (fun _ : finiteIntermediateSpec k K L ↦ (0 : ℤ)))
      inferInstance i)

/-- The zero-shift flat pullback between Chow groups over nested finite intermediate fields. -/
noncomputable def finiteIntermediateTransition
    {L M : FiniteIntermediateField k K} (h : L ≤ M) :
    finiteIntermediateObject k K X i L ⟶ finiteIntermediateObject k K X i M :=
  AddCommGrpCat.ofHom
      ((@ChowGroup.iteratedBaseChangeMap
        (Spec (CommRingCat.of k)) (finiteIntermediateSpec k K L)
        (finiteIntermediateSpec k K M) X.left
        (finiteIntermediateDiagram_universallyCatenary k K M : UniversallyCatenary.{u} _)
        X.hom inferInstance (finiteIntermediateStructureMap k K L)
        (finiteIntermediateSpecMap k K h)
        (fun _ : finiteIntermediateSpec k K M ↦ (0 : ℤ))
        (finiteIntermediateStageDimensions k K M) (i + 0) i (add_zero i)).comp
        (@ChowGroup.baseChangePullback
          (finiteIntermediateSpec k K L) (finiteIntermediateSpec k K M)
          (finiteIntermediateBaseChange k K X L).left
          (finiteIntermediateDiagram_universallyCatenary k K L : UniversallyCatenary.{u} _)
          (finiteIntermediateDiagram_universallyCatenary k K M : UniversallyCatenary.{u} _)
          (finiteIntermediateSpecMap k K h) (finiteIntermediateTransitionMaps_flat k K L M h)
          (fun _ : finiteIntermediateSpec k K L ↦ (0 : ℤ))
          (finiteIntermediateStageDimensions k K L)
          (fun _ : finiteIntermediateSpec k K M ↦ (0 : ℤ))
          (finiteIntermediateStageDimensions k K M) 0
          (fun _ _ _ => (add_zero (0 : ℤ)).symm)
          (finiteIntermediateBaseChange k K X L).hom inferInstance i)) ≫
    eqToHom (congrArg (fun q : finiteIntermediateSpec k K M ⟶ Spec (CommRingCat.of k) ↦
      AddCommGrpCat.of
        (@ChowGroup.{u} (pullback X.hom q)
          (@LocallyOfFiniteType.isLocallyNoetherian
            (pullback X.hom q) (finiteIntermediateSpec k K M)
            (pullback.snd X.hom q) inferInstance
            (finiteIntermediateDiagram_universallyCatenary k K
              (OrderDual.toDual M)).toIsLocallyNoetherian)
          ((pullback.snd X.hom q).relativeDimensionFunction
            (fun _ : finiteIntermediateSpec k K M ↦ (0 : ℤ))) inferInstance i))
      (by
        simp only [finiteIntermediateSpecMap, finiteIntermediateStructureMap,
          FieldExtension.specMap, Scheme.AffineBaseChange.specMap, Comparison.baseMap]
        refine (Spec.map_comp (CommRingCat.ofHom (algebraMap k (L.toIntermediateField k K)))
          (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom)).symm.trans ?_
        refine congrArg Spec.map ?_
        exact congrArg CommRingCat.ofHom
          (RingHom.ext fun x => ((IntermediateField.inclusion h).commutes x).symm)))

/-- The transition along an identity inclusion is the identity morphism. -/
theorem finiteIntermediateTransition_id (L : FiniteIntermediateField k K) :
    finiteIntermediateTransition k K X i (le_refl L) = 𝟙 _ := sorry

/-- Chow-group transitions compose along inclusions of finite intermediate fields. -/
theorem finiteIntermediateTransition_comp
    {L M N : FiniteIntermediateField k K} (hLM : L ≤ M) (hMN : M ≤ N) :
    finiteIntermediateTransition k K X i hLM ≫ finiteIntermediateTransition k K X i hMN =
      finiteIntermediateTransition k K X i (hLM.trans hMN) := sorry

/-- The base change of a scheme from the ground field to the full extension. -/
noncomputable abbrev finiteIntermediateLimitBaseChange :
    Over (Spec (CommRingCat.of K)) :=
  (Over.pullback (AlgebraicGeometry.FieldExtension.specMap k K)).obj X

/-- The canonical map from a finite-intermediate Chow group to the Chow group over `K`. -/
noncomputable def finiteIntermediateLeg (L : FiniteIntermediateField k K) :
    finiteIntermediateObject k K X i L ⟶
      AddCommGrpCat.of
        (@ChowGroup.{u} (finiteIntermediateLimitBaseChange k K X).left
          (@LocallyOfFiniteType.isLocallyNoetherian
            (finiteIntermediateLimitBaseChange k K X).left
            (Spec (CommRingCat.of K))
            (finiteIntermediateLimitBaseChange k K X).hom inferInstance
            (@AlgebraicGeometry.instUniversallyCatenarySpec K _ (@instUniversallyCatenaryRingOfField.{u, u} K _)).toIsLocallyNoetherian)
          ((finiteIntermediateLimitBaseChange k K X).hom.relativeDimensionFunction
            (fun _ : Spec (CommRingCat.of K) ↦ (0 : ℤ))) inferInstance i) :=
  AddCommGrpCat.ofHom
      ((@ChowGroup.iteratedBaseChangeMap
        (Spec (CommRingCat.of k)) (finiteIntermediateSpec k K L)
        (Spec (CommRingCat.of K)) X.left (@AlgebraicGeometry.instUniversallyCatenarySpec K _ (@instUniversallyCatenaryRingOfField.{u, u} K _)) X.hom inferInstance
        (finiteIntermediateStructureMap k K L) (finiteIntermediateConeMap k K L)
        (fun _ : Spec (CommRingCat.of K) ↦ (0 : ℤ)) inferInstance
        (i + 0) i (add_zero i)).comp
        (@ChowGroup.baseChangePullback
          (finiteIntermediateSpec k K L) (Spec (CommRingCat.of K))
          (finiteIntermediateBaseChange k K X L).left
          (finiteIntermediateDiagram_universallyCatenary k K L : UniversallyCatenary.{u} _) (@AlgebraicGeometry.instUniversallyCatenarySpec K _ (@instUniversallyCatenaryRingOfField.{u, u} K _))
          (finiteIntermediateConeMap k K L) (finiteIntermediateConeMaps_flat k K L)
          (fun _ : finiteIntermediateSpec k K L ↦ (0 : ℤ))
          (finiteIntermediateStageDimensions k K L)
          (fun _ : Spec (CommRingCat.of K) ↦ (0 : ℤ)) inferInstance 0
          (fun _ _ _ => (add_zero (0 : ℤ)).symm)
          (finiteIntermediateBaseChange k K X L).hom inferInstance i)) ≫
    eqToHom (congrArg (fun q : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) ↦
      AddCommGrpCat.of
        (@ChowGroup.{u} (pullback X.hom q)
          (@LocallyOfFiniteType.isLocallyNoetherian
            (pullback X.hom q) (Spec (CommRingCat.of K))
            (pullback.snd X.hom q) inferInstance
            (@AlgebraicGeometry.instUniversallyCatenarySpec K _ (@instUniversallyCatenaryRingOfField.{u, u} K _)).toIsLocallyNoetherian)
          ((pullback.snd X.hom q).relativeDimensionFunction
            (fun _ : Spec (CommRingCat.of K) ↦ (0 : ℤ))) inferInstance i))
      (by
        simp only [finiteIntermediateConeMap, finiteIntermediateStructureMap,
          FieldExtension.specMap, Scheme.AffineBaseChange.specMap]
        refine (Spec.map_comp (CommRingCat.ofHom (algebraMap k (L.toIntermediateField k K)))
          (CommRingCat.ofHom (L.toIntermediateField k K).val.toRingHom)).symm.trans ?_
        refine congrArg Spec.map ?_
        exact congrArg CommRingCat.ofHom
          (RingHom.ext fun x => ((L.toIntermediateField k K).val.commutes x).symm)))

/-- Transition maps commute with the canonical maps to the Chow group over `K`. -/
theorem finiteIntermediateLeg_naturality
    {L M : FiniteIntermediateField k K} (h : L ≤ M) :
    finiteIntermediateTransition k K X i h ≫ finiteIntermediateLeg k K X i M =
      finiteIntermediateLeg k K X i L := sorry

/-- For an algebraic extension `K / k` and a finite-type `k`-scheme `X`, the Chow group of
`X` after base change to `K` is the filtered colimit of the Chow groups after base change
to finite-dimensional intermediate fields. -/
theorem finiteIntermediate_isFilteredColimit [Algebra.IsAlgebraic k K]
    (Y : AddCommGrpCat.{u})
    (f : ∀ L : FiniteIntermediateField k K, finiteIntermediateObject k K X i L ⟶ Y)
    (hf : ∀ {L M : FiniteIntermediateField k K} (h : L ≤ M),
      finiteIntermediateTransition k K X i h ≫ f M = f L) :
    ∃! g :
      AddCommGrpCat.of
          (@ChowGroup.{u} (finiteIntermediateLimitBaseChange k K X).left
            (@LocallyOfFiniteType.isLocallyNoetherian
              (finiteIntermediateLimitBaseChange k K X).left
              (Spec (CommRingCat.of K))
              (finiteIntermediateLimitBaseChange k K X).hom inferInstance
              (@AlgebraicGeometry.instUniversallyCatenarySpec K _
                (@instUniversallyCatenaryRingOfField.{u, u} K _)).toIsLocallyNoetherian)
            ((finiteIntermediateLimitBaseChange k K X).hom.relativeDimensionFunction
              (fun _ : Spec (CommRingCat.of K) ↦ (0 : ℤ))) inferInstance i) ⟶
        Y,
      ∀ L : FiniteIntermediateField k K, finiteIntermediateLeg k K X i L ≫ g = f L := sorry

end AlgebraicGeometry.ChowGroup.FieldExtension
