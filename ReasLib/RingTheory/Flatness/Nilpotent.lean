module

public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Tor.Ideal.Flip
public import ReasLib.LinearAlgebra.Quotient.ULift
public import ReasLib.LinearAlgebra.Quotient.RestrictScalars
public import ReasLib.RingTheory.Flatness.Tor
public import ReasLib.RingTheory.Ideal.Tensor.Map
public import ReasLib.RingTheory.Ideal.Tensor.ULift

/-!
# Flatness Across Nilpotent Ideals

This leaf packages the tensor-injectivity form of nilpotent-thickening
flatness.  The same-universe `Tor` criterion stays in `Flatness.Tor`; this
leaf supplies its universe-polymorphic consequence by using the reusable
`ULift` transport API.
-/

@[expose] public section

universe u v w x

namespace Module.Flat.Nilpotent

open scoped TensorProduct

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Flatness lifts across a nilpotent ideal when the closed fiber is flat and
ideal tensor multiplication is injective.  This is the universe-polymorphic
tensor formulation of the nilpotent-ideal `Tor` criterion in Stacks `051C`
(3); its exact `Tor` statement remains
`Module.Flat.of_isNilpotent_ideal_of_quotient_flat_of_isZero_tor_one`. -/
@[stacks 051C "(3)"]
theorem of_quotient_flat_of_tensorMul_injective {I : Ideal R}
    (hI : IsNilpotent I)
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (hinj : Function.Injective (I.tensorMul M)) :
    Module.Flat R M := sorry

section

variable {S : Type v} [CommRing S] [Algebra R S]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Stacks `051J`: flatness descends across an injective algebra map when a nilpotent closed
fiber is flat and the tensor base change is flat. -/
@[stacks 051J]
theorem of_injective_algebraMap {I : Ideal R}
    (hI : IsNilpotent I) (hinj : Function.Injective (algebraMap R S))
    (hflat : Module.Flat (R ⧸ I) (N ⧸ (I • (⊤ : Submodule R N))))
    (hbase : Module.Flat S (S ⊗[R] N)) :
    Module.Flat R N := sorry

end

section ExtendedIdeal

variable {S : Type v} [CommRing S] [Algebra R S]
variable {N : Type w} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case) (Stacks `06A5`): if `I` is
nilpotent, the quotient of `N` by the action of the extended ideal
`Ideal.map (algebraMap R S) I` is flat over the corresponding quotient of `S`, and `N` is flat
over `R`, then `N` is flat over `S`. -/
@[stacks 06A5]
theorem of_quotient_flat_of_flat {I : Ideal R}
    (hI : IsNilpotent I)
    (hquot : Module.Flat (S ⧸ Ideal.map (algebraMap R S) I)
      (N ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S N))))
    (hflat : Module.Flat R N) :
    Module.Flat S N := sorry

end ExtendedIdeal

section Tower

variable {S : Type v} {S' : Type w} [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
variable {M : Type x} [AddCommGroup M] [Module S' M]

/-- Flatness over a nilpotent quotient for an `S'`-module gives flatness over the middle
ring `S` after restricting scalars. -/
@[stacks 06A5 "flatness over the middle ring"]
theorem of_quotient_flat_of_flat_tower {I : Ideal R}
    (hI : IsNilpotent I)
    (hquot : Module.Flat (S ⧸ Ideal.map (algebraMap R S) I)
      ((RestrictScalars S S' M) ⧸
        (Ideal.map (algebraMap R S) I •
          (⊤ : Submodule S (RestrictScalars S S' M)))))
    (hflat : Module.Flat R (RestrictScalars R S' M)) :
    Module.Flat S (RestrictScalars S S' M) := sorry

end Tower

end Module.Flat.Nilpotent
