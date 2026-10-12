/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flat.LocallyNilpotent.Fiber
import StacksCheckRecall

/-!
@stack 0CEL
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

section

variable {R : Type u} {S : Type v} {S' : Type w} {M : Type x}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
variable {I : Ideal R}
variable [AddCommGroup M] [Module S' M]
variable [Algebra.FiniteType R S] [Algebra.FinitePresentation R S']
variable [Module.FinitePresentation S' M]

/- Lemma 10.128.10 (Critère de platitude par fibres: locally nilpotent case) (1): flatness over
the middle ring follows from flatness of the quotient fiber and of the base module. -/
@[stacks 0CEL "(1)"]
#check (Module.Flat.LocallyNilpotent.of_fiber_flat (R := R) (S := S) (S' := S') (M := M) :
  ∀ {I : Ideal R}, I.IsLocallyNilpotent →
    Module.Flat (S ⧸ Ideal.map (algebraMap R S) I)
      ((S ⧸ Ideal.map (algebraMap R S) I) ⊗[S] RestrictScalars S S' M) →
    Module.Flat R (RestrictScalars R S' M) →
    Module.Flat S (RestrictScalars S S' M))

/- Lemma 10.128.10 (Critère de platitude par fibres: locally nilpotent case) (2): at every prime
with nontrivial fiber, the corresponding localization of `S` is flat over `R`. -/
@[stacks 0CEL "(2)"]
#check (RingHom.Flat.atPrime_of_locally_nilpotent_fiber
    (R := R) (S := S) (S' := S') (M := M) :
  ∀ {I : Ideal R}, I.IsLocallyNilpotent →
    Module.Flat (S ⧸ Ideal.map (algebraMap R S) I)
      ((S ⧸ Ideal.map (algebraMap R S) I) ⊗[S] RestrictScalars S S' M) →
    Module.Flat R (RestrictScalars R S' M) →
    ∀ (q : PrimeSpectrum S),
      Nontrivial ((RestrictScalars S S' M) ⊗[S] q.asIdeal.ResidueField) →
      (algebraMap R (Localization.AtPrime q.asIdeal)).Flat)

/- Lemma 10.128.10 (Critère de platitude par fibres: locally nilpotent case) (3): under the same
fiber condition, the localization is essentially finitely presented over `R`. -/
@[stacks 0CEL "(3)"]
#check (RingHom.EssFinitePresentation.atPrime_of_locally_nilpotent_fiber
    (R := R) (S := S) (S' := S') (M := M) :
  ∀ {I : Ideal R}, I.IsLocallyNilpotent →
    Module.Flat (S ⧸ Ideal.map (algebraMap R S) I)
      ((S ⧸ Ideal.map (algebraMap R S) I) ⊗[S] RestrictScalars S S' M) →
    Module.Flat R (RestrictScalars R S' M) →
    ∀ (q : PrimeSpectrum S),
      Nontrivial ((RestrictScalars S S' M) ⊗[S] q.asIdeal.ResidueField) →
      RingHom.EssFinitePresentation (algebraMap R (Localization.AtPrime q.asIdeal)))

end
