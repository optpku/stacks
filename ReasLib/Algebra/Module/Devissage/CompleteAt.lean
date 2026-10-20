/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Support
public import ReasLib.Algebra.Module.Devissage.Complete
public import ReasLib.FieldTheory.Transcendence.PurelyTranscendental
public import ReasLib.RingTheory.KrullDimension.Relative

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace Module.Devissage

namespace Stage

/-- The stage module after base change from `R` to the residue field `κ(r)`, regarded as a
module over the stage algebra `B`. -/
def residueBaseChange {R : Type u} [CommRing R] {r : PrimeSpectrum R} (D : Stage R r) :
    ModuleCat.{u} D.B :=
  let MB := (ModuleCat.restrictScalars D.toA.hom.toRingHom).obj D.M.obj
  let MR := (ModuleCat.restrictScalars (algebraMap R D.B)).obj MB
  @ModuleCat.of D.B inferInstance (MR ⊗[R] r.asIdeal.ResidueField) inferInstance
    (@TensorProduct.leftModule R D.B inferInstance inferInstance MR
      r.asIdeal.ResidueField inferInstance inferInstance inferInstance inferInstance inferInstance
      (ModuleCat.sMulCommClass_mk (algebraMap R D.B) MB))

/-- The stage residue base change is the tensor product of the restricted stage module with
`κ(r)` over `R`. -/
theorem residueBaseChange_def {R : Type u} [CommRing R] {r : PrimeSpectrum R}
    (D : Stage R r) :
    (D.residueBaseChange : Type u) =
      ((ModuleCat.restrictScalars (algebraMap R D.B)).obj
          ((ModuleCat.restrictScalars D.toA.hom.toRingHom).obj D.M.obj)) ⊗[R]
        r.asIdeal.ResidueField := sorry

end Stage

/-- A complete dévissage over `r` together with the lifted primes and compatibility laws
determined by a prime `q` above `r`. -/
structure CompleteAt (R : Type u) [CommRing R] (S : FGAlgCat.{u} R)
    (N : FGModuleCat.{u} S.obj) (r : PrimeSpectrum R) (q : PrimeSpectrum S.obj)
    (hq : r.asIdeal = q.asIdeal.comap (algebraMap R S.obj)) where
  /-- The underlying complete dévissage over `r`. -/
  toComplete : Complete R S N r
  /-- The prime `qᵢ` of each `Bᵢ` lying over `r`. -/
  stagePrime (i : Fin (toComplete.last + 1)) : PrimeSpectrum (toComplete.stage i).B
  /-- The unique prime of each `Aᵢ` lying over `qᵢ`. -/
  liftedPrime (i : Fin (toComplete.last + 1)) : PrimeSpectrum (toComplete.stage i).A
  /-- The prime `qᵢ` of every `Bᵢ` lies over `r`. -/
  stagePrime_comap (i : Fin (toComplete.last + 1)) :
    r.asIdeal =
      (stagePrime i).asIdeal.comap
        (algebraMap R (toComplete.stage i).B)
  /-- The lifted prime of `Aᵢ` contracts to `qᵢ`. -/
  liftedPrime_comap (i : Fin (toComplete.last + 1)) :
    (stagePrime i).asIdeal =
      (liftedPrime i).asIdeal.comap (toComplete.stage i).toA.hom.toRingHom
  /-- The lifted prime is the unique prime of `Aᵢ` with the prescribed contraction. -/
  liftedPrime_unique (i : Fin (toComplete.last + 1))
      (q' : PrimeSpectrum (toComplete.stage i).A) :
    (stagePrime i).asIdeal =
        q'.asIdeal.comap (toComplete.stage i).toA.hom.toRingHom →
      q' = liftedPrime i
  /-- The first lifted prime contracts to `q` along the initial map. -/
  initial_comap :
    q.asIdeal =
      (liftedPrime 0).asIdeal.comap toComplete.initial.hom.toRingHom
  /-- Each later lifted prime contracts to `qᵢ` in the preceding stage. -/
  transition_comap (i : Fin toComplete.last) :
    (stagePrime i.castSucc).asIdeal =
      (liftedPrime i.succ).asIdeal.comap
        (toComplete.transition i).hom.toRingHom
  /-- The prime `qᵢ` belongs to the support of the residue base change. -/
  support_mem (i : Fin (toComplete.last + 1)) :
    stagePrime i ∈
      Module.support (toComplete.stage i).B (toComplete.stage i).residueBaseChange
  /-- The canonical residue-field map `κ(r) →+* κ(qᵢ)` is purely transcendental. -/
  residueField_purelyTranscendental (i : Fin (toComplete.last + 1)) :
    (Ideal.ResidueField.map r.asIdeal (stagePrime i).asIdeal
      (algebraMap R (toComplete.stage i).B)
      (stagePrime_comap i)).IsPurelyTranscendental
  /-- The relative dimension of `R → Bᵢ` is the local dimension of the residue-base-change
  support at its distinguished prime. -/
  dimension_eq (i : Fin (toComplete.last + 1)) :
    relativeDimension R (toComplete.stage i).B =
      topologicalKrullDimAt
        (⟨stagePrime i, support_mem i⟩ :
          Module.support (toComplete.stage i).B
            (toComplete.stage i).residueBaseChange)

namespace CompleteAt

/-- Construct a complete dévissage at `q` from an explicit complete dévissage, its lifted
primes, and all defining compatibility laws. -/
def ofComplete {R : Type u} [CommRing R] {S : FGAlgCat.{u} R}
    {N : FGModuleCat.{u} S.obj} {r : PrimeSpectrum R} {q : PrimeSpectrum S.obj}
    {hq : r.asIdeal = q.asIdeal.comap (algebraMap R S.obj)}
    (toComplete : Complete R S N r)
    (stagePrime : ∀ i : Fin (toComplete.last + 1), PrimeSpectrum (toComplete.stage i).B)
    (liftedPrime : ∀ i : Fin (toComplete.last + 1), PrimeSpectrum (toComplete.stage i).A)
    (stagePrime_comap : ∀ i,
      r.asIdeal = (stagePrime i).asIdeal.comap
        (algebraMap R (toComplete.stage i).B))
    (liftedPrime_comap : ∀ i,
      (stagePrime i).asIdeal =
        (liftedPrime i).asIdeal.comap (toComplete.stage i).toA.hom.toRingHom)
    (liftedPrime_unique : ∀ i (q' : PrimeSpectrum (toComplete.stage i).A),
      (stagePrime i).asIdeal =
          q'.asIdeal.comap (toComplete.stage i).toA.hom.toRingHom →
        q' = liftedPrime i)
    (initial_comap :
      q.asIdeal = (liftedPrime 0).asIdeal.comap toComplete.initial.hom.toRingHom)
    (transition_comap : ∀ i : Fin toComplete.last,
      (stagePrime i.castSucc).asIdeal =
        (liftedPrime i.succ).asIdeal.comap (toComplete.transition i).hom.toRingHom)
    (support_mem : ∀ i,
      stagePrime i ∈
        Module.support (toComplete.stage i).B (toComplete.stage i).residueBaseChange)
    (residueField_purelyTranscendental : ∀ i,
      (Ideal.ResidueField.map r.asIdeal (stagePrime i).asIdeal
        (algebraMap R (toComplete.stage i).B)
        (stagePrime_comap i)).IsPurelyTranscendental)
    (dimension_eq : ∀ i,
      relativeDimension R (toComplete.stage i).B =
        topologicalKrullDimAt
          (⟨stagePrime i, support_mem i⟩ :
            Module.support (toComplete.stage i).B
              (toComplete.stage i).residueBaseChange)) :
    CompleteAt R S N r q hq where
  toComplete := toComplete
  stagePrime := stagePrime
  liftedPrime := liftedPrime
  stagePrime_comap := stagePrime_comap
  liftedPrime_comap := liftedPrime_comap
  liftedPrime_unique := liftedPrime_unique
  initial_comap := initial_comap
  transition_comap := transition_comap
  support_mem := support_mem
  residueField_purelyTranscendental := residueField_purelyTranscendental
  dimension_eq := dimension_eq

/-- The prime `qᵢ` as a point of the support of the residue base change. -/
def supportPoint {R : Type u} [CommRing R] {S : FGAlgCat.{u} R}
    {N : FGModuleCat.{u} S.obj} {r : PrimeSpectrum R} {q : PrimeSpectrum S.obj}
    {hq : r.asIdeal = q.asIdeal.comap (algebraMap R S.obj)}
    (D : CompleteAt R S N r q hq) (i : Fin (D.toComplete.last + 1)) :
    Module.support (D.toComplete.stage i).B
      (D.toComplete.stage i).residueBaseChange :=
  ⟨D.stagePrime i, D.support_mem i⟩

/-- The underlying prime of `supportPoint` is `qᵢ`. -/
theorem supportPoint_coe {R : Type u} [CommRing R] {S : FGAlgCat.{u} R}
    {N : FGModuleCat.{u} S.obj} {r : PrimeSpectrum R} {q : PrimeSpectrum S.obj}
    {hq : r.asIdeal = q.asIdeal.comap (algebraMap R S.obj)}
    (D : CompleteAt R S N r q hq) (i : Fin (D.toComplete.last + 1)) :
    (D.supportPoint i : PrimeSpectrum (D.toComplete.stage i).B) =
      D.stagePrime i := sorry

/-- The canonical residue-field homomorphism from `κ(r)` to the residue field of the
distinguished prime at a stage. -/
def residueFieldMap {R : Type u} [CommRing R] {S : FGAlgCat.{u} R}
    {N : FGModuleCat.{u} S.obj} {r : PrimeSpectrum R} {q : PrimeSpectrum S.obj}
    {hq : r.asIdeal = q.asIdeal.comap (algebraMap R S.obj)}
    (D : CompleteAt R S N r q hq) (i : Fin (D.toComplete.last + 1)) :
    r.asIdeal.ResidueField →+* (D.stagePrime i).asIdeal.ResidueField :=
  Ideal.ResidueField.map r.asIdeal (D.stagePrime i).asIdeal
    (algebraMap R (D.toComplete.stage i).B) (D.stagePrime_comap i)

/-- `residueFieldMap` is the canonical residue-field map induced by `R → Bᵢ`. -/
theorem residueFieldMap_def {R : Type u} [CommRing R] {S : FGAlgCat.{u} R}
    {N : FGModuleCat.{u} S.obj} {r : PrimeSpectrum R} {q : PrimeSpectrum S.obj}
    {hq : r.asIdeal = q.asIdeal.comap (algebraMap R S.obj)}
    (D : CompleteAt R S N r q hq) (i : Fin (D.toComplete.last + 1)) :
    D.residueFieldMap i =
      Ideal.ResidueField.map r.asIdeal (D.stagePrime i).asIdeal
        (algebraMap R (D.toComplete.stage i).B) (D.stagePrime_comap i) := sorry

/-- At every stage, the distinguished prime lies over `r`, and its lifted prime is the unique
prime above it. -/
theorem prime_spec {R : Type u} [CommRing R] {S : FGAlgCat.{u} R}
    {N : FGModuleCat.{u} S.obj} {r : PrimeSpectrum R} {q : PrimeSpectrum S.obj}
    {hq : r.asIdeal = q.asIdeal.comap (algebraMap R S.obj)}
    (D : CompleteAt R S N r q hq) (i : Fin (D.toComplete.last + 1)) :
    r.asIdeal =
        (D.stagePrime i).asIdeal.comap
          (algebraMap R (D.toComplete.stage i).B) ∧
      ((D.stagePrime i).asIdeal =
          (D.liftedPrime i).asIdeal.comap (D.toComplete.stage i).toA.hom.toRingHom ∧
        ∀ q' : PrimeSpectrum (D.toComplete.stage i).A,
          (D.stagePrime i).asIdeal =
              q'.asIdeal.comap (D.toComplete.stage i).toA.hom.toRingHom →
            q' = D.liftedPrime i) := sorry

/-- The first lifted prime contracts to `q`, and every later lifted prime contracts to the
distinguished prime of the preceding stage. -/
theorem chain_spec {R : Type u} [CommRing R] {S : FGAlgCat.{u} R}
    {N : FGModuleCat.{u} S.obj} {r : PrimeSpectrum R} {q : PrimeSpectrum S.obj}
    {hq : r.asIdeal = q.asIdeal.comap (algebraMap R S.obj)}
    (D : CompleteAt R S N r q hq) :
    q.asIdeal =
        (D.liftedPrime 0).asIdeal.comap D.toComplete.initial.hom.toRingHom ∧
      ∀ i : Fin D.toComplete.last,
        (D.stagePrime i.castSucc).asIdeal =
          (D.liftedPrime i.succ).asIdeal.comap
            (D.toComplete.transition i).hom.toRingHom := sorry

/-- At every stage, the canonical extension `κ(r) →+* κ(qᵢ)` is purely transcendental. -/
theorem residueField_spec {R : Type u} [CommRing R] {S : FGAlgCat.{u} R}
    {N : FGModuleCat.{u} S.obj} {r : PrimeSpectrum R} {q : PrimeSpectrum S.obj}
    {hq : r.asIdeal = q.asIdeal.comap (algebraMap R S.obj)}
    (D : CompleteAt R S N r q hq) (i : Fin (D.toComplete.last + 1)) :
    (D.residueFieldMap i).IsPurelyTranscendental := sorry

/-- At every stage, the relative dimension of `R → Bᵢ` is the local dimension of the
residue-base-change support at its distinguished point. -/
theorem dimension_spec {R : Type u} [CommRing R] {S : FGAlgCat.{u} R}
    {N : FGModuleCat.{u} S.obj} {r : PrimeSpectrum R} {q : PrimeSpectrum S.obj}
    {hq : r.asIdeal = q.asIdeal.comap (algebraMap R S.obj)}
    (D : CompleteAt R S N r q hq) (i : Fin (D.toComplete.last + 1)) :
    relativeDimension R (D.toComplete.stage i).B =
      topologicalKrullDimAt (D.supportPoint i) := sorry

end CompleteAt

end Module.Devissage
