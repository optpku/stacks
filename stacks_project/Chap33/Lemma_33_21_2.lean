/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Stalk.Completion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 33.21.2: for a locally algebraic scheme over a field, a separable
formal-power-series presentation of a completed stalk transports along a field extension to the
completed stalk at a base-change point when the two local rings have equal Krull dimension. -/
@[stacks 0C54] #check
  (AlgebraicGeometry.FieldExtension.Stalk.Completion.exists_algEquiv_of_dim_eq_of_isSeparable :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
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
          FieldExtension.Stalk.Completion.Source.completedStalk f y)
      (h_e :
        (((Scheme.completedStalkResidueFieldMap X (FieldExtension.toSource k K f y)).comp
            e.toRingHom).comp
          (algebraMap
            (X.residueField (FieldExtension.toSource k K f y))
            (MvPowerSeries (Fin n)
              (X.residueField (FieldExtension.toSource k K f y)) ⧸ I))) =
          RingHom.id (X.residueField (FieldExtension.toSource k K f y))),
      ∃ eK : FieldExtension.Stalk.Completion.Presentation.quotient f y I ≃ₐ[K]
          FieldExtension.Stalk.Completion.BaseChange.completedStalk f y,
        (((Scheme.completedStalkResidueFieldMap (FieldExtension.baseChange k K f) y).comp
            eK.toRingHom).comp
          (algebraMap
            ((FieldExtension.baseChange k K f).residueField y)
            (FieldExtension.Stalk.Completion.Presentation.quotient f y I))) =
          RingHom.id ((FieldExtension.baseChange k K f).residueField y))
