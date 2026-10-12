/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Completion.Support
import StacksCheckRecall

@[expose] public section

open CategoryTheory DerivedCategory

noncomputable section

universe u

/- Lemma 47.12.5: if `A` is `I`-adically complete, degree-zero cohomology of the
derived `I`-adic completion of `RΓ_Z(M)` is the filtered union of the admissible
`J'`-primary components of `M`. -/
@[stacks 0EEX] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.Completion.cohomologyZeroSupportColimit :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I J : Ideal A)
      [IsAdicComplete I A] (M : ModuleCat.{u} A) [Module.Finite A M]
      (RΓZ : DerivedCategory (ModuleCat.{u} A) ⥤ IdealPowerTorsion J)
      (_ : IdealPowerTorsion.inclusion J ⊣ RΓZ),
      IsIsomorphic
        ((homologyFunctor (ModuleCat.{u} A) 0).obj
          (derivedCompletionOf I I.fg_of_isNoetherianRing
            (RΓZ.obj (ModuleCat.single0 M)).obj))
        (ModuleCat.of A (Ideal.supportColimit I J M)))
