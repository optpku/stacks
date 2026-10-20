module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Stalk.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Stalk.MaximalIdeal
public import ReasLib.AlgebraicGeometry.Scheme.LocalRing.Completion

/-!
# Completed stalks after field extension

This module names the completed local rings and coefficient-extended
formal-power-series presentations attached to a point of a field-extension
base change, and states their transport under a dimension and separability
hypothesis.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.FieldExtension.Stalk.Completion

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

namespace Source

/-- The completed local ring of the source scheme at the image of a point of
its field-extension base change. -/
abbrev completedStalk (y : FieldExtension.baseChange k K f) :=
  AdicCompletion
    (IsLocalRing.maximalIdeal
      (X.presheaf.stalk (FieldExtension.toSource k K f y)))
    (X.presheaf.stalk (FieldExtension.toSource k K f y))

end Source

namespace BaseChange

/-- The completed local ring at a point of a field-extension base change. -/
abbrev completedStalk (y : FieldExtension.baseChange k K f) :=
  AdicCompletion
    (IsLocalRing.maximalIdeal
      ((FieldExtension.baseChange k K f).presheaf.stalk y))
    ((FieldExtension.baseChange k K f).presheaf.stalk y)

end BaseChange

namespace Presentation

/-- Extend a formal-power-series presentation ideal along the residue-field
map induced by a point of a field-extension base change. -/
abbrev ideal
    (y : FieldExtension.baseChange k K f) {n : ℕ}
    (I : Ideal
      (MvPowerSeries (Fin n) (X.residueField (FieldExtension.toSource k K f y)))) :
    Ideal (MvPowerSeries (Fin n) ((FieldExtension.baseChange k K f).residueField y)) :=
  Ideal.map (MvPowerSeries.map ((FieldExtension.toSource k K f).residueFieldMap y).hom) I

/-- The coefficient-extended quotient of a formal-power-series presentation. -/
abbrev quotient
    (y : FieldExtension.baseChange k K f) {n : ℕ}
    (I : Ideal
      (MvPowerSeries (Fin n) (X.residueField (FieldExtension.toSource k K f y)))) :=
  MvPowerSeries (Fin n) ((FieldExtension.baseChange k K f).residueField y) ⧸ ideal f y I

/-- The coefficient-extended presentation quotient is an algebra over the
residue field at the base-change point. -/
instance instResidueAlgebra
    (y : FieldExtension.baseChange k K f) {n : ℕ}
    (I : Ideal
      (MvPowerSeries (Fin n) (X.residueField (FieldExtension.toSource k K f y)))) :
    Algebra ((FieldExtension.baseChange k K f).residueField y) (quotient f y I) :=
  Ideal.Quotient.algebra _

/-- The coefficient-extended presentation quotient is canonically a `K`-algebra. -/
instance instBaseAlgebra
    (y : FieldExtension.baseChange k K f) {n : ℕ}
    (I : Ideal
      (MvPowerSeries (Fin n) (X.residueField (FieldExtension.toSource k K f y)))) :
    Algebra K (quotient f y I) :=
  Ideal.Quotient.algebra K

end Presentation

/-- A separable formal-power-series presentation of a completed source stalk
transports to the completed stalk at a field-extension base-change point when
the two local rings have equal Krull dimension. -/
@[stacks 0C54]
theorem exists_algEquiv_of_dim_eq_of_isSeparable
    [LocallyOfFiniteType f]
    (y : FieldExtension.baseChange k K f)
    (h_dim :
      ringKrullDim (X.presheaf.stalk (FieldExtension.toSource k K f y)) =
        ringKrullDim ((FieldExtension.baseChange k K f).presheaf.stalk y))
    (h_separable :
      Algebra.IsSeparable k (X.residueField (FieldExtension.toSource k K f y)))
    {n : ℕ}
    {I : Ideal
      (MvPowerSeries (Fin n) (X.residueField (FieldExtension.toSource k K f y)))}
    (e :
      (MvPowerSeries (Fin n) (X.residueField (FieldExtension.toSource k K f y)) ⧸ I) ≃ₐ[k]
        Source.completedStalk f y)
    (h_e :
      (((Scheme.completedStalkResidueFieldMap X (FieldExtension.toSource k K f y)).comp
          e.toRingHom).comp
        (algebraMap
          (X.residueField (FieldExtension.toSource k K f y))
          (MvPowerSeries (Fin n) (X.residueField (FieldExtension.toSource k K f y)) ⧸ I))) =
        RingHom.id (X.residueField (FieldExtension.toSource k K f y))) :
    ∃ eK : Presentation.quotient f y I ≃ₐ[K] BaseChange.completedStalk f y,
      (((Scheme.completedStalkResidueFieldMap (FieldExtension.baseChange k K f) y).comp
          eK.toRingHom).comp
        (algebraMap
          ((FieldExtension.baseChange k K f).residueField y)
          (Presentation.quotient f y I))) =
        RingHom.id ((FieldExtension.baseChange k K f).residueField y) := sorry

end AlgebraicGeometry.FieldExtension.Stalk.Completion
