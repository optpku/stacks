/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Chow's lemma

This file packages the diagram supplied by Chow's lemma and states its existence for separated
finite-type morphisms over a Noetherian base.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A Chow modification of `f : X ⟶ S` consists of a proper surjective morphism `π : X' ⟶ X`,
an immersion of `X'` into a relative projective space over `S`, and a dense open of `X` over
which `π` is an isomorphism. -/
structure ChowLemmaModification {X S : Scheme.{u}} (f : X ⟶ S) where
  /-- The dimension of the chosen relative projective space. -/
  n : ℕ
  /-- The chosen relative projective space over `S`. -/
  P : ProjectiveSpaceOver S n
  /-- The source scheme of the proper surjective morphism. -/
  X' : Scheme.{u}
  /-- The morphism from the source scheme to `X`. -/
  π : X' ⟶ X
  /-- The immersion into the chosen relative projective space. -/
  i : X' ⟶ P.scheme
  /-- The morphism to the relative projective space is an immersion. -/
  isImmersion : IsImmersion i
  /-- The immersion and `π` define the same morphism from `X'` to `S`. -/
  commutes : i ≫ P.hom = π ≫ f
  /-- The morphism `π` is proper. -/
  proper : IsProper π
  /-- The morphism `π` is surjective. -/
  surjective : Surjective π
  /-- A dense open of `X` over which `π` is an isomorphism. -/
  denseOpen : X.Opens
  /-- The distinguished open is dense in `X`. -/
  denseOpenDense : Dense (denseOpen : Set X)
  /-- The restriction of `π` over the distinguished dense open is an isomorphism. -/
  isIsoOverDenseOpen : IsIso (π ∣_ denseOpen)

namespace ChowLemmaModification

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- The structure morphism from the chosen relative projective space to the base scheme. -/
def p (M : ChowLemmaModification f) : M.P.scheme ⟶ S :=
  M.P.hom

/-- Constructs a Chow modification from an explicit relative projective-space diagram, a proper
surjective morphism, and a dense open over which that morphism is an isomorphism. -/
def ofProjectiveSpace (n : ℕ) (P : ProjectiveSpaceOver S n) (X' : Scheme.{u})
    (π : X' ⟶ X) (i : X' ⟶ P.scheme) (isImmersion : IsImmersion i)
    (commutes : i ≫ P.hom = π ≫ f) (proper : IsProper π) (surjective : Surjective π)
    (denseOpen : X.Opens) (denseOpenDense : Dense (denseOpen : Set X))
    (isIsoOverDenseOpen : IsIso (π ∣_ denseOpen)) : ChowLemmaModification f where
  n := n
  P := P
  X' := X'
  π := π
  i := i
  isImmersion := isImmersion
  commutes := commutes
  proper := proper
  surjective := surjective
  denseOpen := denseOpen
  denseOpenDense := denseOpenDense
  isIsoOverDenseOpen := isIsoOverDenseOpen

/-- The defining conditions of a Chow modification are immersion and compatibility over the
base, properness and surjectivity of `π`, and an isomorphism over a dense open. -/
theorem conditions_spec (M : ChowLemmaModification f) :
    IsImmersion M.i ∧ M.i ≫ M.p = M.π ≫ f ∧ IsProper M.π ∧ Surjective M.π ∧
      Dense (M.denseOpen : Set X) ∧ IsIso (M.π ∣_ M.denseOpen) := sorry

end ChowLemmaModification

/-- A separated finite-type morphism to a Noetherian scheme admits a Chow modification whose
source immerses into a relative projective space over the base. -/
theorem ChowLemmaModification.exists_of_separated_finiteType
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsSeparated f]
    [Scheme.Hom.FiniteType f] :
    Nonempty (ChowLemmaModification f) := sorry

end AlgebraicGeometry
