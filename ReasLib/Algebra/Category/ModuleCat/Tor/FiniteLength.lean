/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.LocalRing.Length
public import ReasLib.Algebra.Category.ModuleCat.Tor.Notation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tor vanishing for finite-length modules

@stack 00MJ

Vanishing against the residue field of a local ring propagates to every finite-length module in
the first variable. Composition-series and long-exact-sequence arguments remain proof details.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace CategoryTheory.ModuleCat.Tor

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Lemma 10.99.6: if `Tor₁[R](ResidueField R, M)` vanishes, then `Tor₁[R](N, M)`
vanishes for every finite-length module `N`. -/
@[stacks 00MJ "Tor-one vanishing for finite-length modules"]
theorem isZero_one_of_finiteLength_of_residueField
    (hκ : IsZero (Tor₁[R](ResidueField R, M))) (hN : IsFiniteLength R N) :
    IsZero (Tor₁[R](N, M)) := sorry

end CategoryTheory.ModuleCat.Tor
