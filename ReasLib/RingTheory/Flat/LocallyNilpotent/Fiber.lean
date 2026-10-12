/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.EssentialFiniteness.RingHom
public import ReasLib.RingTheory.Flat.Localization.AtPrime.Fiber
public import ReasLib.RingTheory.Ideal.LocallyNilpotent

/-!
# Fiberwise flatness over locally nilpotent thickenings

This leaf records the reusable fiberwise flatness consequences of a locally
nilpotent ideal.  The quotient-fiber hypothesis is stated on its canonical
quotient and tensor-product model, while the three conclusions live in the
namespaces of the properties they establish.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

namespace Module.Flat.LocallyNilpotent

variable {R : Type u} {S : Type v} {S' : Type w} {M : Type x}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
variable {I : Ideal R}
variable [AddCommGroup M] [Module S' M]
variable [Algebra.FiniteType R S] [Algebra.FinitePresentation R S']
variable [Module.FinitePresentation S' M]

/-- Stacks Lemma 10.128.10 (tag `0CEL`): a finitely presented module over a
finite-presentation algebra is flat over the middle algebra when it is flat
over the base and its canonical quotient fiber over a locally nilpotent ideal
is flat. -/
@[stacks 0CEL "(1)"]
theorem of_fiber_flat
    (hI : I.IsLocallyNilpotent)
    (h_fiber : Module.Flat (S ⧸ Ideal.map (algebraMap R S) I)
      ((S ⧸ Ideal.map (algebraMap R S) I) ⊗[S] RestrictScalars S S' M))
    (h_base : Module.Flat R (RestrictScalars R S' M)) :
    Module.Flat S (RestrictScalars S S' M) := sorry

end Module.Flat.LocallyNilpotent

namespace RingHom.Flat

variable {R : Type u} {S : Type v} {S' : Type w} {M : Type x}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
variable {I : Ideal R}
variable [AddCommGroup M] [Module S' M]
variable [Algebra.FiniteType R S] [Algebra.FinitePresentation R S']
variable [Module.FinitePresentation S' M]

/-- Stacks Lemma 10.128.10 (tag `0CEL`): if the residue-field fiber of the
middle restricted module is nontrivial at `q`, then the base map to `S_q` is
flat under the locally nilpotent fiberwise-flatness hypotheses. -/
@[stacks 0CEL "(2)"]
theorem atPrime_of_locally_nilpotent_fiber
    (hI : I.IsLocallyNilpotent)
    (h_fiber : Module.Flat (S ⧸ Ideal.map (algebraMap R S) I)
      ((S ⧸ Ideal.map (algebraMap R S) I) ⊗[S] RestrictScalars S S' M))
    (h_base : Module.Flat R (RestrictScalars R S' M))
    (q : PrimeSpectrum S)
    (hq : Nontrivial ((RestrictScalars S S' M) ⊗[S] q.asIdeal.ResidueField)) :
    (algebraMap R (Localization.AtPrime q.asIdeal)).Flat := sorry

end RingHom.Flat

namespace RingHom.EssFinitePresentation

variable {R : Type u} {S : Type v} {S' : Type w} {M : Type x}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
variable {I : Ideal R}
variable [AddCommGroup M] [Module S' M]
variable [Algebra.FiniteType R S] [Algebra.FinitePresentation R S']
variable [Module.FinitePresentation S' M]

/-- Stacks Lemma 10.128.10 (tag `0CEL`): if the residue-field fiber of the
middle restricted module is nontrivial at `q`, then the local algebra
`R → S_q` is essentially finitely presented under the locally nilpotent
fiberwise-flatness hypotheses. -/
@[stacks 0CEL "(3)"]
theorem atPrime_of_locally_nilpotent_fiber
    (hI : I.IsLocallyNilpotent)
    (h_fiber : Module.Flat (S ⧸ Ideal.map (algebraMap R S) I)
      ((S ⧸ Ideal.map (algebraMap R S) I) ⊗[S] RestrictScalars S S' M))
    (h_base : Module.Flat R (RestrictScalars R S' M))
    (q : PrimeSpectrum S)
    (hq : Nontrivial ((RestrictScalars S S' M) ⊗[S] q.asIdeal.ResidueField)) :
    RingHom.EssFinitePresentation (algebraMap R (Localization.AtPrime q.asIdeal)) := sorry

end RingHom.EssFinitePresentation
