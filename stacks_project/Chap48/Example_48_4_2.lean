module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.OpenRestrictionCounterexample

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped DualNumber

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Example 48.4.2 -/
@[stacks 0A9M] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.dualNumberPolynomial_openRestrictionComparison_not_isIso :
    ∀ (k : Type u) [Field k],
      let R := Polynomial k
      let A := CommRingCat.of R[ε]
      let φ : A ⟶ CommRingCat.of R :=
        CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom
      let Y := Spec A
      let X := Spec (CommRingCat.of R)
      let f : X ⟶ Y := Spec.map φ
      let V : Y.Opens :=
        PrimeSpectrum.basicOpen (TrivSqZeroExt.inl (Polynomial.X : R))
      let U : X.Opens := f ⁻¹ᵁ V
      let M : ℕ → ModuleCat A := fun n ↦
        ModuleCat.of A
          (A ⧸ (DualNumber.epsIdeal R ⊔
            Ideal.span {TrivSqZeroExt.inl ((Polynomial.X : R) ^ (n + 1))}))
      let K₀ : DerivedCategory.{u + 1} (ModuleCat A) :=
        ∐ fun n : ℕ ↦
          ((DerivedCategory.singleFunctor (ModuleCat.{u, u} A) 0).obj (M n))
            ⟦((n + 1 : ℕ) : ℤ)⟧
      let K : DerivedQCoh Y :=
        (@Functor.inv _ _ _ _ (affineGlobalSections A)
          (affineGlobalSectionsIsEquivalence A)).obj K₀
      ∀ (a : DerivedQCoh Y ⥤ DerivedQCoh X)
        (aV : DerivedQCoh V.toScheme ⥤ DerivedQCoh U.toScheme)
        (aAdjunction : pushforwardCohomologyIn f ⊣ a)
        (aVAdjunction : pushforwardCohomologyIn (f ∣_ V) ⊣ aV),
        ¬ IsIso
          ((DerivedBaseChange.mapOfRight
            (pullbackPushforwardAdjunction V.ι)
            (pullbackPushforwardAdjunction U.ι)
            (@asIso _ _ _ _
              (BaseChange.rightMate U.ι (f ∣_ V) f V.ι
                (isPullback_morphismRestrict f V).flip.toCommSq
                a aV aAdjunction aVAdjunction)
              (BaseChange.rightMate_isIso_of_flat
                U.ι (f ∣_ V) f V.ι
                (isPullback_morphismRestrict f V).flip
                a aV aAdjunction aVAdjunction)).inv).app K))

end AlgebraicGeometry.Scheme.DerivedQCoh
