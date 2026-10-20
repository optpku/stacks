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
      (genericPointSpectrumCoproductTo (FieldExtension.baseChange k K X.hom)) := sorry

/-- The generic-point residue-field coproduct of a locally algebraic field-extension base change
is quasi-separated. -/
instance instBaseChangeCoproductQuasiSeparated
    (X : Over (Spec (CommRingCat.of k))) [LocallyAlgebraic X] :
    QuasiSeparated
      (genericPointSpectrumCoproductTo (FieldExtension.baseChange k K X.hom)) := sorry

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
        FieldExtension.Over.toSource k K X := sorry

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
          FieldExtension.Over.toSource k K X := sorry

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
      (FieldExtension.baseChange k K X.hom).normalizationTo := sorry

/-- The first pullback projection of `pullbackComparison` is compatible with the source
normalization map. -/
theorem pullbackComparison_fst_assoc
    (X : Over (Spec (CommRingCat.of k))) [LocallyAlgebraic X] :
    pullbackComparison X ≫
        pullback.fst X.left.normalizationTo
          (FieldExtension.Over.toSource k K X) ≫
        X.left.normalizationTo =
      (FieldExtension.baseChange k K X.hom).normalizationTo ≫
        FieldExtension.Over.toSource k K X := sorry

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
    comparison X ≫ FieldExtension.toSource k K (X.left.normalizationTo ≫ X.hom) = lift X := sorry

/-- The field-extension base projection of `comparison` factors through the normalization map
after field extension. -/
theorem comparison_toBase
    (X : Over (Spec (CommRingCat.of k))) [LocallyAlgebraic X] :
    comparison X ≫ FieldExtension.toBase k K (X.left.normalizationTo ≫ X.hom) =
      (FieldExtension.baseChange k K X.hom).normalizationTo ≫
        FieldExtension.toBase k K X.hom := sorry

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
