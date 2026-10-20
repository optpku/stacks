/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Dimension.LocallyAlgebraic
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Limits.Presentation
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.RingTheory.RingHom.PurelyInseparable

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- For a finite-type scheme `X` over a field `K` and a point `x`, a strict
henselization of the stalk receives the separable closure of the rational
function field in `a = SchemeOverField.baseFieldTrdegAt X x` variables. Its
residue field is purely inseparable over that field, and the strict
henselization is a filtered colimit of finite-type algebras of Krull dimension
at most `d - a`, where `d` is the local topological dimension at `x`. -/
theorem exists_separable_map_and_filtered_colimit
    {K : Type u} [Field K]
    (X : SchemeOverField K) [Algebraic X] (x : X.left)
    (Ash : Type u) [CommRing Ash]
    [Algebra (SchemeOverField.stalkRing X x) Ash]
    [IsStrictHenselizationOf (SchemeOverField.stalkRing X x) Ash] :
    let a := SchemeOverField.baseFieldTrdegAt X x
    let d := (topologicalKrullDimAt x).unbotD 0 |>.toNat
    let Ksep :=
      SeparableClosure
        (FractionRing (MvPolynomial (Fin a) K))
    ∃ (φ : Ksep →+* Ash),
      ((IsLocalRing.residue Ash).comp φ).IsPurelyInseparable ∧
      ∃ (Aash : CommAlgCat Ksep) (e : (Aash : Type u) ≃+* Ash),
        e.toRingHom.comp (algebraMap Ksep Aash) = φ ∧
        ∃ (J : Type u) (_ : Category.{u} J) (_ : IsFiltered J)
          (P : ColimitPresentation J Aash),
          ∀ j, Algebra.FiniteType Ksep (P.diag.obj j) ∧
            ringKrullDim (P.diag.obj j) ≤
              ((d - a : ℕ) : WithBot ℕ∞) := sorry

end AlgebraicGeometry
