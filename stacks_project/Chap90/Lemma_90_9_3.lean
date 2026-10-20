module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Classical
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Smooth

/-!
# Smoothness of restricted coyoneda of a complete local algebra

For `R` in `Ĉ_Λ`, smoothness of `underline R |_{C_Λ}` is equivalent to
maximal-adic formal smoothness and the flat closed-fiber criteria over the
image field of the base. In the classical case these are also equivalent
to a finite-variable power series presentation over the base.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat
open scoped TensorProduct

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/- Lemma 90.9.3. The four smoothness conditions for a complete local algebra are equivalent. -/
@[stacks 0DYL] #check (CompleteLocalAlgCat.isSmooth_tfae :
  ∀ R : CompleteLocalAlgCat Λ k,
    List.TFAE
      [Functor.IsSmooth (CategoryOfElements.π (restrictedCoyoneda R)),
        (algebraMap Λ R.carrier).formally_smooth_for_adic (IsLocalRing.maximalIdeal R.carrier),
        (algebraMap Λ R.carrier).Flat ∧
          Algebra.IsGeometricallyRegular (Algebra.residueImage Λ k)
            (R.carrier ⊗[Λ] Algebra.residueImage Λ k),
        (algebraMap Λ R.carrier).Flat ∧
          (algebraMap (Algebra.residueImage Λ k)
              (R.carrier ⊗[Λ] Algebra.residueImage Λ k)).formally_smooth_for_adic
            (specialFiberAdicIdeal R)])

#check (CompleteLocalAlgCat.isSmooth_tfae_isClassical :
  ∀ [IsClassical Λ k] (R : CompleteLocalAlgCat Λ k),
    List.TFAE
      [Functor.IsSmooth (CategoryOfElements.π (restrictedCoyoneda R)),
        (algebraMap Λ R.carrier).formally_smooth_for_adic (IsLocalRing.maximalIdeal R.carrier),
        (algebraMap Λ R.carrier).Flat ∧
          Algebra.IsGeometricallyRegular (Algebra.residueImage Λ k)
            (R.carrier ⊗[Λ] Algebra.residueImage Λ k),
        (algebraMap Λ R.carrier).Flat ∧
          (algebraMap (Algebra.residueImage Λ k)
              (R.carrier ⊗[Λ] Algebra.residueImage Λ k)).formally_smooth_for_adic
            (specialFiberAdicIdeal R),
        IsPowerSeriesOver (fromClassical R)])

variable [IsClassical Λ k] (R : CompleteLocalAlgCat Λ k)

#check (CompleteLocalAlgCat.isPowerSeriesOver_iff (fromClassical R) :
  IsPowerSeriesOver (fromClassical R) ↔
    ∃ n : ℕ, ∃ e : R ≅ classical.mvPowerSeries n,
      fromClassical R ≫ e.hom = classical.mvPowerSeriesC n)

end CompleteLocalAlgCat
