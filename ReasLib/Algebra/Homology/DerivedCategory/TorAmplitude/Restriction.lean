module

public import ReasLib.Algebra.Category.ModuleCat.RingHom
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tor amplitude under restriction of scalars

@stack 066J
@stack 066K

For an explicit ring homomorphism `f : A →+* B`, restricting a complex with Tor amplitude
`[a, b]` shifts the lower endpoint by a Tor-dimension bound for the target of `f` as an
`A`-module.  The flat case is the degree-zero specialization.  Both statements use the canonical
target module and derived restriction functor, so no ambient `Algebra A B` instance is needed.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.DerivedCategory.HasTorAmplitudeIn

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Lemma 15.67.12 (Stacks `066K`): a Tor-dimension bound for the target module controls the
lower endpoint of Tor amplitude after restriction of scalars. -/
@[stacks 066K "Tor amplitude under finite-Tor-dimension restriction"]
theorem restrictScalars_of_torDimensionLE
    (f : A →+* B) (K : DerivedCategory (ModuleCat B))
    {a b : ℤ} {d : ℕ}
    (hf : ModuleCat.HasTorDimensionLE (R := A) f.targetModule d)
    (hK : HasTorAmplitudeIn (R := B) K a b) :
    HasTorAmplitudeIn (R := A)
      ((ModuleCat.derivedRestrictionOfScalars f).obj K) (a - (d : ℤ)) b := sorry
/- Proof strategy: compare an `A`-linear tensor test after restriction with a `B`-linear test
whose first factor is derived-extended along `f`; combine the target module's interval
`[-d, 0]` with the interval `[a, b]`. -/

/-- Lemma 15.67.11 (Stacks `066J`): restriction along a flat ring homomorphism preserves a
fixed Tor-amplitude interval. -/
@[stacks 066J "Tor amplitude under flat restriction"]
theorem restrictScalars_of_flat
    (f : A →+* B) (hf : f.Flat) (K : DerivedCategory (ModuleCat B))
    {a b : ℤ} (hK : HasTorAmplitudeIn (R := B) K a b) :
    HasTorAmplitudeIn (R := A)
      ((ModuleCat.derivedRestrictionOfScalars f).obj K) a b := sorry
/- Proof strategy: convert `hf` to Tor dimension at most zero for `f.targetModule`, apply
`restrictScalars_of_torDimensionLE` with `d = 0`, and simplify the lower endpoint. -/

end CategoryTheory.DerivedCategory.HasTorAmplitudeIn
