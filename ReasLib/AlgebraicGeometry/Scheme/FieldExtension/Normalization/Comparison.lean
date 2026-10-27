/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.IrreducibleComponents
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Normalization.GenericPoints
public import ReasLib.FieldTheory.Separable.Generated

/-!
# Normalization comparison under field extension

This leaf owns the canonical morphism from the normalization after a field
extension to the field extension of the source normalization.  The pullback
model and its projection formulas remain available for constructions that
need to inspect the comparison before applying its geometric properties.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FieldExtension.Normalization

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The generic-point residue-field coproduct of a locally algebraic field-extension base change
is quasi-compact. -/
instance instBaseChangeCoproductQuasiCompact
    (X : Over (Spec (CommRingCat.of k))) [LocallyAlgebraic X] :
    QuasiCompact
      (genericPointSpectrumCoproductTo (FieldExtension.baseChange k K X.hom)) := by
  classical
  let Y := FieldExtension.baseChange k K X.hom
  let F := fun η : genericPoints Y ↦ Spec (Y.residueField η.1)
  letI : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (FieldExtension.toBase k K X.hom)
  rw [quasiCompact_iff_forall_isAffineOpen]
  intro U hU
  let I : Set (genericPoints Y) := {η | η.1 ∈ U}
  have hfinite : I.Finite := by
    letI : IsAffine (U : Scheme) := hU
    letI : IsNoetherian (U : Scheme) :=
      { toIsLocallyNoetherian := inferInstance
        toCompactSpace := inferInstance }
    have hfiniteU : Finite (genericPoints (U : Scheme)) :=
      genericPoints.finite finite_irreducibleComponents_of_isNoetherian
    let restrictGeneric : I → genericPoints (U : Scheme) := fun η ↦
      ⟨⟨η.1.1, η.2⟩, by
        let f : ↥(U : Scheme) → Y := Subtype.val
        have hf : Topology.IsOpenEmbedding f := U.2.isOpenEmbedding_subtypeVal
        have hpre := preimage_mem_irreducibleComponents η.1.2 hf
          ⟨η.1.1, subset_closure (Set.mem_singleton _), ⟨⟨η.1.1, η.2⟩, rfl⟩⟩
        change closure ({⟨η.1.1, η.2⟩} : Set (U : Scheme)) ∈
          irreducibleComponents (U : Scheme)
        convert hpre using 1
        rw [hf.isOpenMap.preimage_closure_eq_closure_preimage hf.continuous]
        congr 1
        ext z
        change (z = ⟨η.1.1, η.2⟩ ↔ z.1 = η.1.1)
        exact ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩⟩
    exact @Finite.of_injective _ _ hfiniteU restrictGeneric fun η ξ h ↦
      Subtype.ext (Subtype.ext (congrArg (fun z ↦ z.1.1) h))
  have hleg (η : genericPoints Y) (x : F η) :
      genericPointSpectrumCoproductTo Y (Limits.Sigma.ι F η x) = η.1 := by
    exact (congrArg (fun f : Spec (Y.residueField η.1) ⟶ Y ↦ f x)
      (genericPointSpectrumCoproductTo_ι Y η)).trans
        (Scheme.fromSpecResidueField_apply η.1 x)
  have hpreimage :
      genericPointSpectrumCoproductTo Y ⁻¹' (U : Set Y) =
        ⋃ η ∈ I, Set.range (Limits.Sigma.ι F η) := by
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨⟨η, x⟩, rfl⟩ := (sigmaMk F).surjective z
      have hη : η ∈ I := by
        change η.1 ∈ (U : Set Y)
        simpa only [Set.mem_preimage, sigmaMk_mk, hleg] using hz
      exact Set.mem_iUnion_of_mem η (Set.mem_iUnion_of_mem hη
        ⟨x, (sigmaMk_mk F η x).symm⟩)
    · intro z hz
      obtain ⟨η, hz⟩ := Set.mem_iUnion.mp hz
      obtain ⟨hη, x, rfl⟩ := Set.mem_iUnion.mp hz
      change genericPointSpectrumCoproductTo Y (Limits.Sigma.ι F η x) ∈ U
      rw [hleg]
      exact hη
  change IsCompact (genericPointSpectrumCoproductTo Y ⁻¹' (U : Set Y))
  rw [hpreimage]
  exact hfinite.isCompact_biUnion fun η _ ↦ isCompact_range (Limits.Sigma.ι F η).continuous

/-- The generic-point residue-field coproduct of a locally algebraic field-extension base change
is quasi-separated. -/
instance instBaseChangeCoproductQuasiSeparated
    (X : Over (Spec (CommRingCat.of k))) [LocallyAlgebraic X] :
    QuasiSeparated
      (genericPointSpectrumCoproductTo (FieldExtension.baseChange k K X.hom)) := by
  let Y := FieldExtension.baseChange k K X.hom
  have : IsLocallyNoetherian (genericPointSpectrumCoproduct Y) := by
    change IsLocallyNoetherian (∐ fun η : genericPoints Y ↦ Spec (Y.residueField η.1))
    rw [isLocallyNoetherian_iff_openCover (sigmaOpenCover _)]
    intro η
    change IsLocallyNoetherian (Spec (Y.residueField η.1))
    infer_instance
  exact QuasiSeparated.of_quasiSeparatedSpace _

set_option backward.isDefEq.respectTransparency false in
/-- The canonical lift from the normalization after field extension to the source normalization. -/
def lift
    (X : Over (Spec (CommRingCat.of k))) [LocallyAlgebraic X] :
    (FieldExtension.baseChange k K X.hom).normalization ⟶ X.left.normalization :=
  let Y := FieldExtension.baseChange k K X.hom
  let π : Y ⟶ X.left := FieldExtension.Over.toSource k K X
  let genericMap : genericPoints Y → genericPoints X.left := fun η ↦
    ⟨π η.1, by
      have hcomponent := FieldExtension.Irreducible.image_component k K X.hom
        (genericPoints.component η)
      have hgeneric := (genericPoints.isGenericPoint η).image π.continuous
      change closure {π η.1} ∈ irreducibleComponents X.left
      rw [hgeneric.def,
        (isClosed_of_mem_irreducibleComponents _ hcomponent).closure_eq]
      exact hcomponent⟩
  let genericMapHom : genericPointSpectrumCoproduct Y ⟶
      genericPointSpectrumCoproduct X.left :=
    Limits.Sigma.desc fun η ↦
      Spec.map (π.residueFieldMap η.1) ≫
        eqToHom (congrArg (fun x ↦ Spec (X.left.residueField x))
          (show π η.1 = (genericMap η).1 by
            change π η.1 = π η.1
            rfl)) ≫
        Limits.Sigma.ι
          (fun ξ : genericPoints X.left ↦ Spec (X.left.residueField ξ.1))
          (genericMap η)
  have genericMapHom_over :
      genericMapHom ≫ genericPointSpectrumCoproductTo X.left =
        genericPointSpectrumCoproductTo Y ≫ π := by
    apply Limits.Sigma.hom_ext
    intro η
    simp [genericMapHom, genericMap, π]
    exact (genericPointSpectrumCoproductTo_ι Y η).symm =≫ π
  let toPullback : genericPointSpectrumCoproduct Y ⟶
      pullback X.left.normalizationTo π :=
    pullback.lift
      (genericMapHom ≫
        (genericPointSpectrumCoproductTo X.left).toNormalization)
      (genericPointSpectrumCoproductTo Y)
      (by simpa [Category.assoc] using genericMapHom_over)
  (genericPointSpectrumCoproductTo Y).normalizationDesc
      toPullback (pullback.snd X.left.normalizationTo π)
        (pullback.lift_snd _ _ _).symm ≫
    pullback.fst X.left.normalizationTo π

/-- The canonical lift lies over the composite of the normalization map after field extension
and the source projection. -/
theorem lift_spec
    (X : Over (Spec (CommRingCat.of k))) [LocallyAlgebraic X] :
    lift X ≫ X.left.normalizationTo =
      (FieldExtension.baseChange k K X.hom).normalizationTo ≫
        FieldExtension.Over.toSource k K X := by
  dsimp only [lift]
  rw [Category.assoc, pullback.condition, ← Category.assoc,
    Scheme.Hom.normalizationDesc_comp]

/-- A morphism to the source normalization satisfying the lift equation is the canonical lift. -/
theorem lift_unique
    (X : Over (Spec (CommRingCat.of k))) [LocallyAlgebraic X]
    (h : (FieldExtension.baseChange k K X.hom).normalization ⟶ X.left.normalization)
    (hh : h ≫ X.left.normalizationTo =
      (FieldExtension.baseChange k K X.hom).normalizationTo ≫
        FieldExtension.Over.toSource k K X) :
    h = lift X := sorry

/-- The normalization after field extension has a unique morphism to the source normalization
over the source scheme. -/
theorem existsUniqueLift
    (X : Over (Spec (CommRingCat.of k))) [LocallyAlgebraic X] :
    ∃! h : (FieldExtension.baseChange k K X.hom).normalization ⟶ X.left.normalization,
      h ≫ X.left.normalizationTo =
        (FieldExtension.baseChange k K X.hom).normalizationTo ≫
          FieldExtension.Over.toSource k K X := by
  exact ⟨lift X, lift_spec X, fun h hh ↦ lift_unique X h hh⟩

/-- The pullback-model comparison from the normalization after field extension to the pullback
of the source normalization along the source projection. -/
noncomputable def pullbackComparison
    (X : Over (Spec (CommRingCat.of k))) [LocallyAlgebraic X] :
    (FieldExtension.baseChange k K X.hom).normalization ⟶
      pullback X.left.normalizationTo
        ((FieldExtension.Over.toSource k K X) :
          (FieldExtension.Over.baseChange k K X).left ⟶ X.left) :=
  pullback.lift
    (lift X)
    (FieldExtension.baseChange k K X.hom).normalizationTo
    (lift_spec X)

/-- The second pullback projection of `pullbackComparison` is the normalization map after
field extension. -/
theorem pullbackComparison_snd
    (X : Over (Spec (CommRingCat.of k))) [LocallyAlgebraic X] :
    pullbackComparison X ≫
        pullback.snd X.left.normalizationTo
          (FieldExtension.Over.toSource k K X) =
      (FieldExtension.baseChange k K X.hom).normalizationTo := by
  exact pullback.lift_snd ..

/-- The first pullback projection of `pullbackComparison` is compatible with the source
normalization map. -/
theorem pullbackComparison_fst_assoc
    (X : Over (Spec (CommRingCat.of k))) [LocallyAlgebraic X] :
    pullbackComparison X ≫
        pullback.fst X.left.normalizationTo
          (FieldExtension.Over.toSource k K X) ≫
        X.left.normalizationTo =
      (FieldExtension.baseChange k K X.hom).normalizationTo ≫
        FieldExtension.Over.toSource k K X := by
  rw [pullbackComparison, pullback.lift_fst_assoc]
  exact lift_spec X

/-- The canonical comparison from the normalization after field extension to the field extension
of the source normalization. -/
@[stacks 0C3N]
noncomputable def comparison
    (X : Over (Spec (CommRingCat.of k))) [LocallyAlgebraic X] :
    (FieldExtension.baseChange k K X.hom).normalization ⟶
      FieldExtension.baseChange k K (X.left.normalizationTo ≫ X.hom) :=
  pullbackComparison X ≫
    (pullbackRightPullbackFstIso X.hom (FieldExtension.specMap k K)
      X.left.normalizationTo).hom

/-- The field-extension source projection of `comparison` is the canonical lift. -/
theorem comparison_toSource
    (X : Over (Spec (CommRingCat.of k))) [LocallyAlgebraic X] :
    comparison X ≫ FieldExtension.toSource k K (X.left.normalizationTo ≫ X.hom) = lift X := by
  calc
    _ = pullbackComparison X ≫
        pullback.fst X.left.normalizationTo (FieldExtension.Over.toSource k K X) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun f ↦ pullbackComparison X ≫ f)
          (pullbackRightPullbackFstIso_hom_fst X.hom (FieldExtension.specMap k K)
            X.left.normalizationTo))
    _ = lift X := pullback.lift_fst ..

/-- The field-extension base projection of `comparison` factors through the normalization map
after field extension. -/
theorem comparison_toBase
    (X : Over (Spec (CommRingCat.of k))) [LocallyAlgebraic X] :
    comparison X ≫ FieldExtension.toBase k K (X.left.normalizationTo ≫ X.hom) =
      (FieldExtension.baseChange k K X.hom).normalizationTo ≫
        FieldExtension.toBase k K X.hom := by
  calc
    _ = pullbackComparison X ≫
        pullback.snd X.left.normalizationTo (FieldExtension.Over.toSource k K X) ≫
          FieldExtension.toBase k K X.hom :=
      (Category.assoc _ _ _).trans
        (congrArg (fun f ↦ pullbackComparison X ≫ f)
          (pullbackRightPullbackFstIso_hom_snd X.hom (FieldExtension.specMap k K)
            X.left.normalizationTo))
    _ = _ := (Category.assoc _ _ _).symm.trans
      (congrArg (fun f ↦ f ≫ FieldExtension.toBase k K X.hom)
        (pullbackComparison_snd X))

/-- If the field extension is separable, the normalization comparison is an isomorphism. -/
@[stacks 0C3N]
instance comparison_isIso_of_isSeparable
    (X : Over (Spec (CommRingCat.of k))) [LocallyAlgebraic X]
    [Algebra.IsSeparableOver k K] :
    IsIso
      ((comparison X) :
        (FieldExtension.baseChange k K X.hom).normalization ⟶
          FieldExtension.baseChange k K (X.left.normalizationTo ≫ X.hom)) := sorry

/-- For every field extension, the normalization comparison is a universal homeomorphism. -/
@[stacks 0C3N]
instance comparison_universalHomeomorphism
    (X : Over (Spec (CommRingCat.of k))) [LocallyAlgebraic X] :
    UniversalHomeomorphism
      ((comparison X) :
        (FieldExtension.baseChange k K X.hom).normalization ⟶
          FieldExtension.baseChange k K (X.left.normalizationTo ≫ X.hom)) := sorry

end AlgebraicGeometry.FieldExtension.Normalization
