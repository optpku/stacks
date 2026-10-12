/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.EssentialFiniteness.Basic
public import ReasLib.Algebra.Category.ModuleCat.Tor.Notation
public import ReasLib.Algebra.Category.ModuleCat.Tor.Ideal
import StacksCheckRecall

/-!
Lemma 10.128.7 (0471): flatness detected by a quotient and Tor₁ criterion.

@stack 0471
-/

@[expose] public section

open CategoryTheory.Limits
open scoped TensorProduct

universe u v

section

variable {R : Type u} {S : Type v} {M : Type u}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.FinitePresentation S M]

/- The approximation and local-criterion declarations used in the proof are intentionally kept
   out of this source-facing statement file; the public surface records the textbook criterion. -/

/-- Lemma 10.128.7: let `R → S` be a local homomorphism of local rings, let `I ≠ R` be an ideal of
`R`, and let `M` be an `S`-module. If `S` is essentially of finite presentation over `R`, `M` is
of finite presentation over `S`, `Tor₁^R(M, R ⧸ I)` vanishes, and `M ⧸ I • ⊤` is flat over
`R ⧸ I`, then `M` is flat over `R`. -/
@[stacks 0471]
theorem flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal_of_essFinitePresentation
    (hess : (algebraMap R S).EssFinitePresentation)
    (I : Ideal R) (hI : I ≠ ⊤)
    (hTor : IsZero (Tor₁[R](M, R ⧸ I)))
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))) :
    Module.Flat R M := sorry

#check @RingHom.EssFinitePresentation
#check @Module.Flat
#check @CategoryTheory.ModuleCat.Tor.isZero_oneQuotient_iff

end
