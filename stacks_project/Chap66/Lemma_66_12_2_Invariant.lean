module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.Subobject.Basic
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Invariant
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Pullback
public import stacks_project.Chap65.Definition_65_9_3_EtaleEquivalence

/-!
# Invariant immersions for scheme pre-relations

An `R`-invariant locally closed subscheme of `U` is a scheme `Z` over the base together with an
immersion `Z ⟶ U` whose associated subobject is invariant under the source and target maps of
`R`.
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

/-- An `R`-invariant locally closed subscheme of `U` is an immersion into `U` whose subobject is
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

namespace InvariantImmersion

variable {S : Scheme.{u}} {U : Over S} {P : PreRelation U}

/-- The invariant immersion determined by an immersion `ι : Z ⟶ U` whose subobject is invariant
under `P`. -/
def ofι {Z : Over S} (ι : Z ⟶ U) [h : AlgebraicGeometry.IsImmersion ι.left]
    (hInv : P.IsInvariant (subobjectMk ι)) : InvariantImmersion P where
  Z := Z
  ι := ι
  isImmersion := h
  isInvariant := hInv

/-- The inclusion of an invariant immersion is an immersion, is invariant as a subobject, and is
a monomorphism. -/
theorem spec (Z' : InvariantImmersion P) :
    AlgebraicGeometry.IsImmersion Z'.ι.left ∧
      P.IsInvariant (@subobjectMk _ _ _ Z'.ι Z'.isImmersion) ∧
      Mono Z'.ι.left := sorry

/-- The subobject of `U.left` represented by an invariant immersion. -/
def subobject (Z' : InvariantImmersion P) : Subobject U.left :=
  @subobjectMk _ _ _ Z'.ι Z'.isImmersion

/-- The subobject of an invariant immersion is `subobjectMk` of its inclusion. -/
theorem subobject_eq (Z' : InvariantImmersion P) :
    Z'.subobject = @subobjectMk _ _ _ Z'.ι Z'.isImmersion := sorry

/-- The restriction of `P` to an invariant immersion. -/
def restrictedRelation (Z' : InvariantImmersion P) : PreRelation Z'.Z :=
  P.pullback Z'.ι

/-- The restricted relation of `Z'` is the pullback of `P` along `Z'.ι`. -/
theorem restrictedRelation_eq (Z' : InvariantImmersion P) :
    Z'.restrictedRelation = P.pullback Z'.ι := sorry

/-- The restriction of an étale equivalence relation along an invariant immersion remains an
étale equivalence relation, because invariance identifies `R'` with both fibre products
`R ×_{s, U} Z'` and `Z' ×_{U, t} R`. -/
theorem restrictedRelation_isEtaleEquivalence (Z' : InvariantImmersion P)
    [P.IsEtaleEquivalenceRelation] :
    (P.pullback Z'.ι).IsEtaleEquivalenceRelation := sorry

end InvariantImmersion

end AlgebraicGeometry.Scheme.PreRelation
