module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat base change in a local square

@stack 0GEB
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

universe u v w x y

section

variable {R : Type u} {S : Type v} {R' : Type w} {S' : Type x}
variable [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
variable [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S']
variable [algRS' : Algebra R S']
variable [towerRSS' : IsScalarTower R S S'] [towerRR'S' : IsScalarTower R R' S']
variable [localR : IsLocalRing R] [localS : IsLocalRing S]
variable [localR' : IsLocalRing R'] [localS' : IsLocalRing S']
variable [localRS : IsLocalHom (algebraMap R S)]
variable [localRR' : IsLocalHom (algebraMap R R')]
variable [localSS' : IsLocalHom (algebraMap S S')]
variable [localR'S' : IsLocalHom (algebraMap R' S')]
variable [noetherianR' : IsNoetherianRing R'] [noetherianS' : IsNoetherianRing S']
variable {M : Type y} [AddCommGroup M] [Module S M] [Module R M]
variable [towerRSM : IsScalarTower R S M] [finiteM : Module.Finite S M]

include algRS' towerRSS' towerRR'S'
include localR localS localR' localS' localRS localRR' localSS' localR'S'
include noetherianR' noetherianS' towerRSM finiteM

namespace Module.Flat.LocalSquare

/-- Lemma 10.100.2: in a commutative square of local homomorphisms, flat horizontal maps
transport a finite module that is flat over the lower-left ring to a module flat over the
lower-right ring, provided the lower maximal ideal extends to the lower-right maximal ideal. -/
@[stacks 0GEB]
theorem baseChange_of_maximalIdeal_eq
    (hbase : (algebraMap R R').Flat) (htarget : (algebraMap S S').Flat)
    (hM : Module.Flat R M)
    (hmax : Ideal.map (algebraMap R R') (maximalIdeal R) = maximalIdeal R') :
    Module.Flat R' (S' ⊗[S] M) := sorry

end Module.Flat.LocalSquare

end
