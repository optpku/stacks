/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.Subobject.Basic
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Invariant
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.EtaleEquivalenceRelation

/-!
# Invariant immersions for scheme pre-relations

An invariant locally closed subscheme is an immersion whose associated subobject is invariant
under the source and target maps of the relation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- The subobject of `U.left` represented by an immersion `ι : Z ⟶ U` over `S`. -/
def subobjectMk {S : Scheme.{u}} {U Z : Over S} (ι : Z ⟶ U)
    [AlgebraicGeometry.IsImmersion ι.left] : Subobject U.left :=
  Subobject.mk ι.left

/-- Given an immersion instance, `subobjectMk ι` agrees with `Subobject.mk ι.left`. -/
theorem subobjectMk_eq_mk {S : Scheme.{u}} {U Z : Over S} (ι : Z ⟶ U)
    [AlgebraicGeometry.IsImmersion ι.left] :
    subobjectMk ι = Subobject.mk ι.left := sorry

/-- An invariant locally closed subscheme of `U` is an immersion into `U` whose subobject is
invariant under `P`. -/
structure InvariantImmersion {S : Scheme.{u}} {U : Over S} (P : PreRelation U) where
  /-- The scheme over `S` underlying the invariant subscheme. -/
  Z : Over S
  /-- The inclusion of the invariant subscheme into `U`. -/
  ι : Z ⟶ U
  /-- The inclusion is an immersion of schemes. -/
  isImmersion : AlgebraicGeometry.IsImmersion ι.left
  /-- The subscheme is invariant under the source and target maps of `P`. -/
  isInvariant : P.IsInvariant (@subobjectMk _ _ _ ι isImmersion)

attribute [instance] InvariantImmersion.isImmersion
attribute [instance 100] IsEtaleEquivalenceRelation.isEquivalenceRelation

namespace InvariantImmersion

variable {S : Scheme.{u}} {U : Over S} {P : PreRelation U}

/-- The invariant immersion determined by an immersion whose subobject is invariant. -/
def ofι {Z : Over S} (ι : Z ⟶ U) [immersion : AlgebraicGeometry.IsImmersion ι.left]
    (invariant : P.IsInvariant (subobjectMk ι)) : InvariantImmersion P where
  Z := Z
  ι := ι
  isImmersion := immersion
  isInvariant := invariant

/-- The inclusion of an invariant immersion is an immersion, is invariant as a subobject, and is
a monomorphism. -/
theorem spec (Z' : InvariantImmersion P) :
    AlgebraicGeometry.IsImmersion Z'.ι.left ∧
      P.IsInvariant (@subobjectMk _ _ _ Z'.ι Z'.isImmersion) ∧
      Mono Z'.ι.left := sorry

/-- The subobject of `U.left` represented by an invariant immersion. -/
def subobject (Z' : InvariantImmersion P) : Subobject U.left :=
  subobjectMk Z'.ι

/-- The subobject of an invariant immersion is `subobjectMk` of its inclusion. -/
theorem subobject_eq (Z' : InvariantImmersion P) :
    Z'.subobject = @subobjectMk _ _ _ Z'.ι Z'.isImmersion := sorry

/-- Two invariant immersions are equivalent when they represent the same subscheme. -/
def subobjectSetoid (P : PreRelation U) : Setoid (InvariantImmersion P) where
  r first second := first.subobject = second.subobject
  iseqv := ⟨fun _ => rfl, fun equality => equality.symm,
    fun first second => first.trans second⟩

/-- Invariant locally closed subschemes, independent of their chosen immersion presentations. -/
def SubobjectClass (P : PreRelation U) := Quotient (subobjectSetoid P)

/-- The restriction of `P` to an invariant immersion. -/
def restrictedRelation (Z' : InvariantImmersion P) : PreRelation Z'.Z :=
  P.pullback Z'.ι

/-- The restricted relation of `Z'` is the pullback of `P` along `Z'.ι`. -/
theorem restrictedRelation_eq (Z' : InvariantImmersion P) :
    Z'.restrictedRelation = P.pullback Z'.ι := sorry

/-- Restricting an étale equivalence relation to an invariant immersion gives an étale
equivalence relation. -/
theorem restrictedRelation_isEtaleEquivalence (Z' : InvariantImmersion P)
    [P.IsEtaleEquivalenceRelation] :
    AlgebraicGeometry.Scheme.PreRelation.IsEtaleEquivalenceRelation (P.pullback Z'.ι) := sorry

/-- The target projection of the restriction of an étale equivalence relation to an invariant
immersion is étale. -/
theorem restrictedRelation_etale_t (Z' : InvariantImmersion P)
    [P.IsEtaleEquivalenceRelation] : AlgebraicGeometry.Etale (P.pullback Z'.ι).t.left :=
  (restrictedRelation_isEtaleEquivalence Z').etale_t

/-- The source projection of the restriction of an étale equivalence relation to an invariant
immersion is étale. -/
theorem restrictedRelation_etale_s (Z' : InvariantImmersion P)
    [P.IsEtaleEquivalenceRelation] : AlgebraicGeometry.Etale (P.pullback Z'.ι).s.left :=
  (restrictedRelation_isEtaleEquivalence Z').etale_s

end InvariantImmersion

end AlgebraicGeometry.Scheme.PreRelation
