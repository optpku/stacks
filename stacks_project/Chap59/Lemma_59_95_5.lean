module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Dimension.StrictHenselization
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 59.95.5: if `X` is of finite type over a field `K`, then at a point `x`
there is a map from the separable closure of the rational function field with
`a = trdeg_K κ(x)` variables to a strict henselization of the stalk.  Its
residue field is purely inseparable over that field, and the strict
henselization is presented as a filtered colimit of finite-type algebras whose
Krull dimensions are bounded by `d - a`, where `d = dim_x X`. -/
@[stacks 0F0U] #check (AlgebraicGeometry.exists_separable_map_and_filtered_colimit :
  ∀ {K : Type u} [Field K]
    (X : SchemeOverField K) [Algebraic X] (x : X.left)
    (Ash : Type u) [CommRing Ash]
    [Algebra (SchemeOverField.stalkRing X x) Ash]
    [IsStrictHenselizationOf (SchemeOverField.stalkRing X x) Ash],
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
              ((d - a : ℕ) : WithBot ℕ∞))

end AlgebraicGeometry
