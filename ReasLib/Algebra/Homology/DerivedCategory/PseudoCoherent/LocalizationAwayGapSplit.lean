module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.LocalizationAwaySplit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Gap splitting after principal localization

@stack 068U

Vanishing of one residue-field homology group is the gap specialization of the local splitting
criterion.  After shrinking to a principal neighborhood, the localized complex splits across
that degree and its upper term is perfect with the expected lower Tor-amplitude bound.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure
open scoped DerivedTensorWithAlgebra

universe u

-- Local instance justification (search instability): the source decomposition uses the
-- standard t-structure on the derived category of modules.
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

variable {R : Type u} [CommRing R]
variable (𝔭 : PrimeSpectrum R)

local notation "κ" => 𝔭.asIdeal.ResidueField
local notation "Hκ" => DerivedCategory.homologyFunctor (ModuleCat κ)

/-- Lemma 15.77.4 (068U): if degree-`i` homology vanishes after derived extension to the residue
field at `𝔭`, then some principal localization away from `𝔭` splits across degree `i`; the upper
term is perfect with Tor-amplitude bounded below by `i + 1`. -/
@[stacks 068U "localized gap splitting from residue-field homology vanishing"]
theorem exists_localizationAway_gapSplit_of_residueField_homology_isZero
    (K : DerivedCategory (ModuleCat R)) (i : ℤ) (hK : K.IsPseudoCoherent)
    (hHi : IsZero ((Hκ i).obj (K ⊗[R]^L[κ]))) :
    ∃ f : R, f ∉ 𝔭.asIdeal ∧
      ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f])).IsPerfect ∧
        DerivedCategory.HasTorAmplitudeGE (R := Localization.Away f)
          ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]))
          (i + 1) ∧
          ∃! e :
              K ⊗[R]^L[Localization.Away f] ≅
                (t.truncLE (i - 1)).obj (K ⊗[R]^L[Localization.Away f]) ⊞
                  (t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]),
            ((t.truncLEι (i - 1)).app (K ⊗[R]^L[Localization.Away f])) ≫ e.hom =
                biprod.inl ∧
              e.hom ≫ biprod.snd =
                ((t.truncGEπ (i + 1)).app
                  (K ⊗[R]^L[Localization.Away f])) := sorry

end CategoryTheory
