module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Normalization

/-!
# Normalization after a field extension

This leaf owns the normalized base change of an algebraic scheme over a field.
It records the finiteness hypotheses needed by the generic-point normalization
construction before packaging the resulting scheme over the extension field.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.FieldExtension.Normalization

variable {k : Type u} [Field k]

/-- Field extension preserves the locally finite type structure of an algebraic scheme. -/
theorem baseChange_locallyOfFiniteType
    (X : Over (Spec (CommRingCat.of k))) [Algebraic X] (K : Type u)
    [Field K] [Algebra k K] :
    LocallyOfFiniteType (FieldExtension.Over.baseChange k K X).hom := sorry

/-- The field extension of an algebraic scheme has finite irreducible components on compact
opens. -/
theorem baseChange_finiteComponents
    (X : Over (Spec (CommRingCat.of k))) [Algebraic X] (K : Type u)
    [Field K] [Algebra k K] :
    Scheme.HasFiniteIrreducibleComponentsOnCompactOpens
      (FieldExtension.baseChange k K X.hom) := sorry

/-- The generic-point residue-field coproduct of an algebraic field extension base change is
quasi-compact. -/
theorem baseChange_genericPoints_quasiCompact
    (X : Over (Spec (CommRingCat.of k))) [Algebraic X] (K : Type u)
    [Field K] [Algebra k K] :
    QuasiCompact
      (genericPointSpectrumCoproductTo (FieldExtension.baseChange k K X.hom)) := sorry

/-- The generic-point residue-field coproduct of an algebraic field extension base change is
quasi-separated. -/
theorem baseChange_genericPoints_quasiSeparated
    (X : Over (Spec (CommRingCat.of k))) [Algebraic X] (K : Type u)
    [Field K] [Algebra k K] :
    QuasiSeparated
      (genericPointSpectrumCoproductTo (FieldExtension.baseChange k K X.hom)) := sorry

/-- The normalization of the field-extension base change of an algebraic scheme, presented over
the extension field. -/
noncomputable def baseChange
    (X : Over (Spec (CommRingCat.of k))) (K : Type u)
    [Field K] [Algebra k K] [Algebraic X] : Over (Spec (CommRingCat.of K)) :=
  -- Local instance justification (defeq pin): select the recorded quasi-compactness proof for
  -- the generic-point normalization morphism used below.
  letI : QuasiCompact
      (genericPointSpectrumCoproductTo (FieldExtension.baseChange k K X.hom)) :=
    baseChange_genericPoints_quasiCompact X K
  -- Local instance justification (defeq pin): select the recorded quasi-separatedness proof for
  -- the generic-point normalization morphism used below.
  letI : QuasiSeparated
      (genericPointSpectrumCoproductTo (FieldExtension.baseChange k K X.hom)) :=
    baseChange_genericPoints_quasiSeparated X K
  Over.mk
    ((FieldExtension.baseChange k K X.hom).normalizationTo ≫
      (FieldExtension.Over.baseChange k K X).hom)

end AlgebraicGeometry.FieldExtension.Normalization
