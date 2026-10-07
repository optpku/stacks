module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.LocalizationAwaySplit
public import ReasLib.RingTheory.Spectrum.Prime.Localization.Away
import Mathlib.Tactic.CrossRefAttribute

/-!
# Three-term local splitting of pseudo-coherent complexes

@stack 0A1V

Surjectivity of the residue-field homology comparisons in two adjacent degrees produces a single
principal neighborhood on which the complex splits into its lower truncation, localized middle
homology, and perfect upper truncation.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure
open scoped DerivedTensorWithAlgebra

universe u

-- Local instance justification (search instability): all truncations use the standard
-- t-structure on the derived category of modules.
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

variable {R : Type u} [CommRing R]
variable (𝔭 : PrimeSpectrum R)

local notation "κ" => 𝔭.asIdeal.ResidueField
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "Away" => LocalizedModule.Away

/-- Lemma 15.77.3 (0A1V): surjectivity of the two adjacent residue-field homology comparisons
yields one principal localization on which the upper truncation is perfect with its lower
Tor-amplitude bound, the middle homology is finite free, and the localized complex has the
canonical three-term decomposition. -/
@[stacks 0A1V "three-term splitting from adjacent homology surjectivity"]
theorem exists_localizationAway_threeTermSplit_of_residueField_homology_surjective
    (K : DerivedCategory (ModuleCat R)) (i : ℤ) (hK : K.IsPseudoCoherent)
    (hsurj_i : Epi
      (ModuleCat.derivedExtensionHomologyComparison (algebraMap R κ) K i))
    (hsurj_im1 : Epi
      (ModuleCat.derivedExtensionHomologyComparison (algebraMap R κ) K (i - 1))) :
    ∃ f : R,
      ∃ e :
        K ⊗[R]^L[Localization.Away f] ≅
          ((t.truncLE (i - 1)).obj (K ⊗[R]^L[Localization.Away f]) ⊞
              ((DerivedCategory.singleFunctor (ModuleCat (Localization.Away f)) i).obj
                (ModuleCat.of (Localization.Away f) (Away f ((H i).obj K))))) ⊞
            (t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]),
        f ∉ 𝔭.asIdeal ∧
          ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f])).IsPerfect ∧
            DerivedCategory.HasTorAmplitudeGE (R := Localization.Away f)
              ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]))
              (i + 1) ∧
              Module.Free (Localization.Away f) (Away f ((H i).obj K)) ∧
                Module.Finite (Localization.Away f) (Away f ((H i).obj K)) := sorry

end CategoryTheory
