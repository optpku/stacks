module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.FieldTheory.GeometricRegularity
public import ReasLib.RingTheory.Smooth.Adic.Basic
public import stacks_project.Chap90.Definition_90_6_1_Prorepresentable
public import stacks_project.Chap90.Definition_90_9_1_Smooth
public import stacks_project.Chap90.Lemma_90_3_4_Length
public import stacks_project.Chap90.Lemma_90_8_6_PowerSeries
public import stacks_project.Chap90.Lemma_90_9_3_Classical
public import stacks_project.Chap90.Remark_90_7_6_TypesCompletion

/-!
# Smoothness of restricted coyoneda of a complete local algebra

For `R` in `Ĉ_Λ`, smoothness of `underline R |_{C_Λ}` is equivalent to
`m_R`-adic formal smoothness of `Λ → R`, and to the closed-fiber criteria
over `k' = residueImage Λ k`. In the classical case these are also equivalent
to `R` being a finite-variable power series ring over `Λ`.
-/

@[expose] public section

open CategoryTheory IsLocalRing ArtinianLocalAlgCat
open scoped TensorProduct

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- The special fiber `R.carrier ⊗[Λ] residueImage Λ k` is a `residueImage Λ k`-algebra
via the right tensor-factor action. -/
instance instAlgebra_specialFiber (R : CompleteLocalAlgCat Λ k) :
    Algebra (Algebra.residueImage Λ k) (R.carrier ⊗[Λ] Algebra.residueImage Λ k) :=
  Algebra.TensorProduct.rightAlgebra

/-- The `m_R`-adic ideal on the special fiber, obtained by extending
`maximalIdeal R.carrier` along `Algebra.TensorProduct.includeLeftRingHom`. -/
def specialFiberAdicIdeal (R : CompleteLocalAlgCat Λ k) :
    Ideal (R.carrier ⊗[Λ] Algebra.residueImage Λ k) :=
  Ideal.map Algebra.TensorProduct.includeLeftRingHom (maximalIdeal R.carrier)

/-- The special-fiber adic ideal is the extension of `maximalIdeal R.carrier`. -/
theorem specialFiberAdicIdeal_eq (R : CompleteLocalAlgCat Λ k) :
    specialFiberAdicIdeal R =
      Ideal.map Algebra.TensorProduct.includeLeftRingHom (maximalIdeal R.carrier) :=
  sorry

/-- Lemma 90.9.3 (1): Let `R` be an object of `CompleteLocalAlgCat Λ k`. The following
are equivalent: `CategoryOfElements.π (restrictedCoyoneda R)` is smooth;
`algebraMap Λ R.carrier` is formally smooth in the `maximalIdeal R.carrier`-adic
topology; `algebraMap Λ R.carrier` is flat and `R.carrier ⊗[Λ] residueImage Λ k`
is geometrically regular over `residueImage Λ k`; and `algebraMap Λ R.carrier` is
flat and `algebraMap (residueImage Λ k) (R.carrier ⊗[Λ] residueImage Λ k)` is
formally smooth in the `m_R`-adic topology. -/
@[stacks 0DYL]
theorem isSmooth_tfae (R : CompleteLocalAlgCat Λ k) :
    List.TFAE
      [Functor.IsSmooth (CategoryOfElements.π (restrictedCoyoneda R)),
        (algebraMap Λ R.carrier).formally_smooth_for_adic (maximalIdeal R.carrier),
        (algebraMap Λ R.carrier).Flat ∧
          Algebra.IsGeometricallyRegular (Algebra.residueImage Λ k)
            (R.carrier ⊗[Λ] Algebra.residueImage Λ k),
        (algebraMap Λ R.carrier).Flat ∧
          (algebraMap (Algebra.residueImage Λ k)
              (R.carrier ⊗[Λ] Algebra.residueImage Λ k)).formally_smooth_for_adic
            (specialFiberAdicIdeal R)] :=
  sorry

/-- Smoothness of `CategoryOfElements.π (restrictedCoyoneda R)` is equivalent to
`m_R`-adic formal smoothness of `algebraMap Λ R.carrier`. -/
theorem isSmooth_iff_formallySmooth (R : CompleteLocalAlgCat Λ k) :
    Functor.IsSmooth (CategoryOfElements.π (restrictedCoyoneda R)) ↔
      (algebraMap Λ R.carrier).formally_smooth_for_adic (maximalIdeal R.carrier) :=
  sorry

/-- `m_R`-adic formal smoothness of `algebraMap Λ R.carrier` is equivalent to
flatness together with geometric regularity of the special fiber over
`residueImage Λ k`. -/
theorem formallySmooth_iff_flat_isGeometricallyRegular (R : CompleteLocalAlgCat Λ k) :
    (algebraMap Λ R.carrier).formally_smooth_for_adic (maximalIdeal R.carrier) ↔
      (algebraMap Λ R.carrier).Flat ∧
        Algebra.IsGeometricallyRegular (Algebra.residueImage Λ k)
          (R.carrier ⊗[Λ] Algebra.residueImage Λ k) :=
  sorry

/-- `m_R`-adic formal smoothness of `algebraMap Λ R.carrier` is equivalent to
flatness together with `m_R`-adic formal smoothness of the special fiber map
`residueImage Λ k → R.carrier ⊗[Λ] residueImage Λ k`. -/
theorem formallySmooth_iff_flat_formallySmooth_specialFiber
    (R : CompleteLocalAlgCat Λ k) :
    (algebraMap Λ R.carrier).formally_smooth_for_adic (maximalIdeal R.carrier) ↔
      (algebraMap Λ R.carrier).Flat ∧
        (algebraMap (Algebra.residueImage Λ k)
            (R.carrier ⊗[Λ] Algebra.residueImage Λ k)).formally_smooth_for_adic
          (specialFiberAdicIdeal R) :=
  sorry

/-- Lemma 90.9.3 (2): in the classical case, the equivalents of `isSmooth_tfae`
are also equivalent to `IsPowerSeriesOver (fromClassical R)`. -/
@[stacks 0DYL]
theorem isSmooth_tfae_isClassical [IsClassical Λ k] (R : CompleteLocalAlgCat Λ k) :
    List.TFAE
      [Functor.IsSmooth (CategoryOfElements.π (restrictedCoyoneda R)),
        (algebraMap Λ R.carrier).formally_smooth_for_adic (maximalIdeal R.carrier),
        (algebraMap Λ R.carrier).Flat ∧
          Algebra.IsGeometricallyRegular (Algebra.residueImage Λ k)
            (R.carrier ⊗[Λ] Algebra.residueImage Λ k),
        (algebraMap Λ R.carrier).Flat ∧
          (algebraMap (Algebra.residueImage Λ k)
              (R.carrier ⊗[Λ] Algebra.residueImage Λ k)).formally_smooth_for_adic
            (specialFiberAdicIdeal R),
        IsPowerSeriesOver (fromClassical R)] :=
  sorry

/-- In the classical case, smoothness of `CategoryOfElements.π (restrictedCoyoneda R)`
is equivalent to `IsPowerSeriesOver (fromClassical R)`. -/
theorem isSmooth_iff_isPowerSeriesOver [IsClassical Λ k]
    (R : CompleteLocalAlgCat Λ k) :
    Functor.IsSmooth (CategoryOfElements.π (restrictedCoyoneda R)) ↔
      IsPowerSeriesOver (fromClassical R) :=
  sorry

/-- `IsPowerSeriesOver (fromClassical R)` unpacks to an isomorphism
`R ≅ classical.mvPowerSeries n` over `classical.mvPowerSeriesC n`. -/
theorem isPowerSeriesOver_fromClassical_iff [IsClassical Λ k]
    (R : CompleteLocalAlgCat Λ k) :
    IsPowerSeriesOver (fromClassical R) ↔
      ∃ n : ℕ, ∃ e : R ≅ classical.mvPowerSeries n,
        fromClassical R ≫ e.hom = classical.mvPowerSeriesC n :=
  sorry

end CompleteLocalAlgCat
