/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.FinitePresentation.Localization
public import ReasLib.Algebra.Module.LocalizedModule.Finite
import StacksCheckRecall

@[expose] public section

/-!
# Finite and Finitely Presented Modules at a Prime

The two clauses are specializations at `p.primeCompl` of the generic
localized-module owners imported directly from ReasLib.

@stack 05GJ
-/

universe u v

section

variable {R : Type u} [CommRing R]
variable (p : Ideal R) [p.IsPrime]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable [Module.Finite (Localization p.primeCompl) (LocalizedModule p.primeCompl M)]

/- Lemma 10.126.5 (1): if `Mₚ` is finite over `Rₚ`, there is a finite
`R`-module `M'` mapping to `M` whose localization at `p` is equivalent to `Mₚ`. -/
@[stacks 05GJ "(1), finite localized module at a prime"]
#check Module.Finite.exists_model_of_localized (R := R) (M := M) p.primeCompl

-- The lower-level finite-submodule formulation remains available to consumers that need it.
#check Submodule.exists_finite_of_localized_eq_top (R := R) (M := M) p.primeCompl

end

section

variable {R : Type u} [CommRing R]
variable (p : Ideal R) [p.IsPrime]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable [Module.FinitePresentation (Localization p.primeCompl)
  (LocalizedModule p.primeCompl M)]

/- Lemma 10.126.5 (2): finite presentation at a prime is the
`p.primeCompl` specialization of the generic localized presentation model. -/
@[stacks 05GJ "(2), finitely presented localized module at a prime"]
#check Module.FinitePresentation.exists_model_of_localized (A := R) (N := M) p.primeCompl

end
