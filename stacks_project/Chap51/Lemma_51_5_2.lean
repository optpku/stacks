/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap51.Lemma_51_5_2_SpecializationSupport
import StacksCheckRecall

universe u

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)

/- Lemma 51.5.2: for a Noetherian commutative ring `A` and a
specialization-stable subset `T ⊆ PrimeSpectrum A`, total right-derived
supported sections `RH⁰_T` is right adjoint to the derived inclusion
`D(Mod_{A,T}) ⟶ D(A)`. -/
@[stacks 0EF0] #check
  (CategoryTheory.ModuleCat.SupportedOn.derivedAdjunctionOfNoetherianStable T hT :
    CategoryTheory.ModuleCat.SupportedOn.derivedInclusion T ⊣
      CategoryTheory.ModuleCat.SupportedOn.derivedSections T)

end
