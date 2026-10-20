module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tor-amplitude of a tensor product after restriction of scalars

@stack 0B66

For an explicit ring homomorphism `f : A →+* B`, a Tor-amplitude interval over `B` and a
Tor-amplitude interval over `A` add under derived tensor product over `B`, after restricting the
result to `A`.  Keeping `f` explicit avoids an ambient `Algebra` parameter and makes the theorem
usable by later change-of-rings arguments.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped DerivedTensorProduct

universe u

namespace CategoryTheory.DerivedCategory.HasTorAmplitudeIn

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Lemma 15.67.10 (Stacks `0B66`): Tor-amplitude intervals add under tensor product over the
target ring, after restricting the result along `f`. -/
@[stacks 0B66 "Tor-amplitude of a restricted derived tensor product"]
theorem tensor_restrictScalars
    (f : A →+* B) (K L : DerivedCategory (ModuleCat B))
    {a b c d : ℤ}
    (hK : HasTorAmplitudeIn (R := B) K a b)
    (hL : HasTorAmplitudeIn (R := A)
      ((ModuleCat.derivedRestrictionOfScalars f).obj L) c d) :
    HasTorAmplitudeIn (R := A)
      ((ModuleCat.derivedRestrictionOfScalars f).obj (K ⊗[B]^L L))
      (a + c) (b + d) := sorry
/- Proof strategy: rewrite every `A`-linear tensor test through the derived
restriction/tensor comparison, then combine the two input support intervals using associativity
of derived tensor product. -/

end CategoryTheory.DerivedCategory.HasTorAmplitudeIn
