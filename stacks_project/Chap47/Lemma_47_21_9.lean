/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Gorenstein.Tor
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleTor

universe u

namespace LinearMap.IsInjectiveHull

/- Lemma 47.21.9 (1): For an injective hull `E` of the residue field of a local
Gorenstein ring of Krull dimension `d`, `Tor⁽i⁾[A](E, IsLocalRing.ResidueField A)`
is zero whenever `i ≠ d`. -/
@[stacks 0EBT] #check
  (LinearMap.IsInjectiveHull.tor_isZero_of_ne_krullDim :
    ∀ {A E : Type u} [CommRing A] [IsLocalRing A] [IsGorensteinLocalRing A]
      [AddCommGroup E] [Module A E] [Module.Injective A E]
      {ι : IsLocalRing.ResidueField A →ₗ[A] E},
      ι.IsInjectiveHull → ∀ (d i : ℕ), ringKrullDim A = d → i ≠ d →
        IsZero (Tor⁽i⁾[A](E, IsLocalRing.ResidueField A)))

/- Lemma 47.21.9 (2): For an injective hull `E` of the residue field of a local
Gorenstein ring of Krull dimension `d`, the degree-`d` Tor object is isomorphic to
the residue field. -/
@[stacks 0EBT] #check
  (LinearMap.IsInjectiveHull.tor_iso_residueField :
    ∀ {A E : Type u} [CommRing A] [IsLocalRing A] [IsGorensteinLocalRing A]
      [AddCommGroup E] [Module A E] [Module.Injective A E]
      {ι : IsLocalRing.ResidueField A →ₗ[A] E},
      ι.IsInjectiveHull → ∀ (d : ℕ), ringKrullDim A = d →
        Nonempty
          (Tor⁽d⁾[A](E, IsLocalRing.ResidueField A) ≅
            ModuleCat.of A (IsLocalRing.ResidueField A)))

end LinearMap.IsInjectiveHull
