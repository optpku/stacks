/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta

/-!
# Quasi-isomorphisms and the Berthelot-Ogus eta operator

The eta operator preserves quasi-isomorphisms between nonnegative complexes on which the chosen
scalar acts regularly degreewise.  This is the natural statement for the `ℕ`-indexed eta owner;
an unrestricted `ℤ`-indexed version requires a genuine negative-power or divided-differential
model and is intentionally not encoded with `Int.toNat`.

@stack 0F7Q
-/

@[expose] public section

open HomologicalComplex
open scoped nonZeroDivisors

universe u v

namespace CochainComplex.BerthelotOgus.Nat

variable {A : Type u} [CommRing A]

/-- The Berthelot-Ogus eta map associated to a quasi-isomorphism of termwise
`f`-torsion-free nonnegative complexes is a quasi-isomorphism.  For this image-submodule model,
degreewise regularity is the essential hypothesis; no separate regularity assumption on `A` is
needed. -/
theorem map_quasiIso (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℕ} (φ : K ⟶ L)
    [QuasiIso φ] (hK : IsTermwiseTorsionFree f K)
    (hL : IsTermwiseTorsionFree f L) : QuasiIso (map f φ) := sorry

/-- Lemma 15.96.3, tag `0F7Q`, in the nonnegative eta model: if `f` is a nonzerodivisor,
`φ : K ⟶ L` is a quasi-isomorphism, and both complexes are termwise `f`-torsion-free, then
`η_f φ` is a quasi-isomorphism. -/
@[stacks 0F7Q "Berthelot-Ogus eta preserves quasi-isomorphisms"]
theorem map_quasiIso_of_nonZeroDivisor
    (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℕ} (φ : K ⟶ L)
    (hf : f ∈ nonZeroDivisors A) [QuasiIso φ]
    (hK : IsTermwiseTorsionFree f K) (hL : IsTermwiseTorsionFree f L) :
    QuasiIso (map f φ) := sorry

end CochainComplex.BerthelotOgus.Nat
