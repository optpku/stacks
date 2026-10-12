/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import ReasLib.RingTheory.RingHom.IndEtale.Henselian

/-!
# Ind-etale lifting through a common residue field

This leaf gives the common-field presentation of the residue-point lifting
property of an ind-etale algebra over a henselian local ring.  The residue
point itself remains owned by `RingHom.ResiduePoint`.

@stack 08HR
-/

@[expose] public section

open IsLocalRing

universe u v w x

namespace RingHom.IndEtale

variable {R : Type u} {A : Type v} {T : Type w} {K : Type x}
variable [CommRing R] [CommRing A] [CommRing T] [Field K]
variable [Algebra R A] [Algebra R T] [Algebra R K]
variable [Algebra A K] [Algebra T K]
variable [IsScalarTower R A K] [IsScalarTower R T K]
variable [IsLocalRing A] [HenselianLocalRing T]
variable [IsLocalHom (algebraMap A K)] [IsLocalHom (algebraMap T K)]

/-- Tag 08HR: an ind-etale `R`-algebra has a unique `R`-algebra map to a henselian local
`R`-algebra when their local maps to a common field are compatible and the target map identifies
that field with its residue field.  This is the common-field formulation of
`existsUnique_lift`; the comparison of maximal-ideal residue fields is derived through `K`. -/
@[stacks 08HR "common residue-field lift"]
theorem existsUnique_lift_of_commonResidueField
    (hA : (algebraMap R A).IndEtale)
    (hK : Function.Bijective (ResidueField.lift (algebraMap T K))) :
    ∃! f : A →ₐ[R] T, (algebraMap T K).comp (f : A →+* T) = algebraMap A K := sorry

section AlgEquiv

variable [HenselianLocalRing A]
variable {S' : Type w}
variable [CommRing S'] [Algebra R S'] [Algebra S' K]
variable [IsScalarTower R S' K]
variable [HenselianLocalRing S']
variable [IsLocalHom (algebraMap S' K)]

/-- Tag 08HT: two henselian local `R`-algebras that are ind-etale over `R`
and identify a common field `K` with their residue fields are uniquely
isomorphic over `R`, compatibly with the maps to `K`. -/
@[stacks 08HT "common residue-field algebra equivalence"]
theorem algEquiv_of_commonResidueField
    (hS : (algebraMap R A).IndEtale)
    (hS' : (algebraMap R S').IndEtale)
    (hκ : Function.Bijective (ResidueField.lift (algebraMap A K)))
    (hκ' : Function.Bijective (ResidueField.lift (algebraMap S' K))) :
    ∃! e : A ≃ₐ[R] S',
      (algebraMap S' K).comp (e : A →+* S') = algebraMap A K := sorry

end AlgEquiv

end RingHom.IndEtale
