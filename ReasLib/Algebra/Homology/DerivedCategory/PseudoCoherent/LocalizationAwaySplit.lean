module

public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.RingTheory.Localization.Away.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Homology
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.TorAmplitude
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local splitting of pseudo-coherent complexes

@stack 0A1U

Surjectivity of the residue-field homology comparison lets one shrink to a principal
neighborhood on which the upper truncation is perfect with the expected lower Tor-amplitude
bound.  The canonical truncation triangle then has a unique compatible biproduct splitting.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure
open scoped DerivedTensorWithAlgebra

universe u

-- Local instance justification (search instability): the truncation functors in this theorem
-- are those of the standard t-structure on the derived category of modules.
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

variable {R : Type u} [CommRing R]
variable (𝔭 : PrimeSpectrum R)

local notation "κ" => 𝔭.asIdeal.ResidueField

/-- Lemma 15.77.2 (0A1U): if the residue-field homology comparison is surjective in degree `i`,
then some principal localization away from `𝔭` makes the upper truncation perfect with
Tor-amplitude bounded below by `i + 1`, and the canonical truncation triangle admits a unique
compatible biproduct splitting. -/
@[stacks 0A1U "local splitting from residue-field homology surjectivity"]
theorem exists_localizationAway_split_of_residueField_homology_surjective
    (K : DerivedCategory (ModuleCat R)) (i : ℤ) (hK : K.IsPseudoCoherent)
    (hsurj : Epi
      (ModuleCat.derivedExtensionHomologyComparison (algebraMap R κ) K i)) :
    ∃ f : R, f ∉ 𝔭.asIdeal ∧
      ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f])).IsPerfect ∧
        DerivedCategory.HasTorAmplitudeGE (R := Localization.Away f)
          ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]))
          (i + 1) ∧
          ∃! e :
              K ⊗[R]^L[Localization.Away f] ≅
                (t.truncLE i).obj (K ⊗[R]^L[Localization.Away f]) ⊞
                  (t.truncGE (i + 1)).obj
                    (K ⊗[R]^L[Localization.Away f]),
            ((t.truncLEι i).app (K ⊗[R]^L[Localization.Away f])) ≫ e.hom =
                biprod.inl ∧
              e.hom ≫ biprod.snd =
                ((t.truncGEπ (i + 1)).app
                  (K ⊗[R]^L[Localization.Away f])) := sorry

end CategoryTheory
