module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Flat.Localization.AtPrime
public import ReasLib.RingTheory.LocalRing.ResidueField.MaximalIdeal
public import ReasLib.RingTheory.RingHom.Flat.FaithfullyFlat

/-!
# Fiberwise Flatness at Prime Localizations

This leaf packages the prime-local fiber arguments used to turn a nontrivial
residue-field fiber into faithful flatness of a localized module, and then
into flatness of the corresponding localized algebra map.  The basic
prime-local flatness predicates remain in `Flat.Localization.AtPrime`; this
child records the additional fiber hypothesis.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

namespace IsLocalRing.ResidueField

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {N : Type v} [AddCommGroup N] [Module A N]

/-- Stacks `06A5`: over a local ring, tensoring a module with the residue
field is nontrivial exactly when quotienting by the maximal-ideal action is
nontrivial. -/
@[stacks 06A5 "closed fiber nontriviality"]
theorem nontrivial_tensor_iff :
    Nontrivial (N ⊗[A] IsLocalRing.ResidueField A) ↔
      Nontrivial (N ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A N))) := sorry

end IsLocalRing.ResidueField

namespace LocalizedModule.AtPrime

variable {A : Type u} [CommRing A]
variable {N : Type v} [AddCommGroup N] [Module A N]

/-- Stacks `06A5`: localizing a nontrivial residue-field fiber at its prime
preserves nontriviality. -/
@[stacks 06A5 "localized fiber nontriviality"]
theorem nontrivial_tensor_residueField (q : PrimeSpectrum A)
    (h : Nontrivial (N ⊗[A] q.asIdeal.ResidueField)) :
    Nontrivial
      (LocalizedModule.AtPrime q.asIdeal N ⊗[Localization.AtPrime q.asIdeal]
        q.asIdeal.ResidueField) := sorry

end LocalizedModule.AtPrime

namespace Module.FaithfullyFlat

variable {A : Type u} [CommRing A]
variable {N : Type v} [AddCommGroup N] [Module A N]

/-- Stacks `06A5`: a flat module with a nontrivial fiber at `q` becomes
faithfully flat after localization at `q`. -/
@[stacks 06A5 "faithfully flat localized fiber"]
theorem atPrime_of_flat_of_nontrivial_fiber (q : PrimeSpectrum A)
    (hflat : Module.Flat A N)
    (h : Nontrivial (N ⊗[A] q.asIdeal.ResidueField)) :
    Module.FaithfullyFlat (Localization.AtPrime q.asIdeal)
      (LocalizedModule.AtPrime q.asIdeal N) := sorry

end Module.FaithfullyFlat

namespace RingHom.Flat

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- Stacks `06A5`: if a module is flat over the base ring and faithfully flat
after localization at `q`, then the algebra map to the local target ring is
flat. -/
@[stacks 06A5 "flatness from a faithfully flat localized module"]
theorem atPrime_of_flat_of_faithfullyFlat (q : PrimeSpectrum S)
    (hflat : Module.Flat R M)
    (hfaithful : Module.FaithfullyFlat (Localization.AtPrime q.asIdeal)
      (LocalizedModule.AtPrime q.asIdeal M)) :
    (algebraMap R (Localization.AtPrime q.asIdeal)).Flat := sorry

/-- Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case) (Stacks `06A5`): if a module
is flat over both `R` and `S` and has a nontrivial residue-field fiber at `q`, then
`R → Localization.AtPrime q.asIdeal` is flat. -/
@[stacks 06A5]
theorem atPrime_of_flat_of_nontrivial_fiber (q : PrimeSpectrum S)
    (hflat_R : Module.Flat R M) (hflat_S : Module.Flat S M)
    (h : Nontrivial (M ⊗[S] q.asIdeal.ResidueField)) :
    (algebraMap R (Localization.AtPrime q.asIdeal)).Flat := sorry

variable {S' : Type w} {M' : Type x}
variable [CommRing S'] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
variable [AddCommGroup M'] [Module S' M']

/-- The prime-fiber flatness criterion for a module presented over a further algebra `S'`, with
the scalar restrictions kept explicit through `RestrictScalars`. -/
@[stacks 06A5 "tower form of localized fiber flatness"]
theorem atPrime_of_flat_of_nontrivial_fiber_tower (q : PrimeSpectrum S)
    (hflat_R : Module.Flat R (RestrictScalars R S' M'))
    (hflat_S : Module.Flat S (RestrictScalars S S' M'))
    (h : Nontrivial ((RestrictScalars S S' M') ⊗[S] q.asIdeal.ResidueField)) :
    (algebraMap R (Localization.AtPrime q.asIdeal)).Flat := sorry

end RingHom.Flat
