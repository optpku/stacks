/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallySmooth
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormallySmooth

/-!
# Formal smoothness via étale scheme squares

A morphism of algebraic spaces is formally smooth if and only if every
commutative square with scheme vertices and étale vertical arrows has
formally smooth top arrow, and if and only if some such square with
surjective vertical arrows does.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FormallySmooth

/-- Every commutative square of schemes over `f` with étale vertical arrows has
formally smooth top arrow in the sense of `AlgebraicGeometry.FormallySmooth`. -/
def forallEtaleSchemeSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∀ {U V : Over S} (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (ψ : U ⟶ V),
    AlgebraicSpace.Etale a → AlgebraicSpace.Etale b →
      CommSq (ofOverMap ψ) a b f → AlgebraicGeometry.FormallySmooth ψ.left

/-- Unfolding of `forallEtaleSchemeSquare`. -/
theorem forallEtaleSchemeSquare_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    forallEtaleSchemeSquare f ↔
      ∀ {U V : Over S} (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (ψ : U ⟶ V),
        AlgebraicSpace.Etale a → AlgebraicSpace.Etale b →
          CommSq (ofOverMap ψ) a b f →
            AlgebraicGeometry.FormallySmooth ψ.left :=
  sorry

/-- There is a commutative square of schemes over `f` with étale surjective
vertical arrows and formally smooth top arrow. -/
def existsSurjectiveEtaleSchemeSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (ψ : U ⟶ V),
    AlgebraicSpace.Etale a ∧ AlgebraicSpace.Etale b ∧
      AlgebraicSpace.Surjective a ∧ AlgebraicSpace.Surjective b ∧
        CommSq (ofOverMap ψ) a b f ∧ AlgebraicGeometry.FormallySmooth ψ.left

/-- Unfolding of `existsSurjectiveEtaleSchemeSquare`. -/
theorem existsSurjectiveEtaleSchemeSquare_iff {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    existsSurjectiveEtaleSchemeSquare f ↔
      ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (ψ : U ⟶ V),
        AlgebraicSpace.Etale a ∧ AlgebraicSpace.Etale b ∧
          AlgebraicSpace.Surjective a ∧ AlgebraicSpace.Surjective b ∧
            CommSq (ofOverMap ψ) a b f ∧
              AlgebraicGeometry.FormallySmooth ψ.left :=
  sorry

/-- Lemma 76.19.10 (1): A morphism of algebraic spaces over `S` is formally
smooth if and only if every commutative square with scheme vertices and étale
vertical arrows has formally smooth top arrow. -/
@[stacks 061K]
theorem iff_forallEtaleSchemeSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : FormallySmooth f ↔ forallEtaleSchemeSquare f :=
  sorry

/-- Lemma 76.19.10 (2): A morphism of algebraic spaces over `S` is formally
smooth if and only if some commutative square with scheme vertices and étale
surjective vertical arrows has formally smooth top arrow. -/
@[stacks 061K]
theorem iff_existsSurjectiveEtaleSchemeSquare {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    FormallySmooth f ↔ existsSurjectiveEtaleSchemeSquare f :=
  sorry

/-- In a commutative square of schemes over a formally smooth morphism of
algebraic spaces, étale vertical arrows make the top arrow formally smooth. -/
theorem etaleSchemeSquare {S : Scheme.{u}} {U V : Over S}
    {X Y : AlgebraicSpace S} {ψ : U ⟶ V} {a : ofOver U ⟶ X} {b : ofOver V ⟶ Y}
    {f : X ⟶ Y} [AlgebraicSpace.Etale a] [AlgebraicSpace.Etale b]
    [FormallySmooth f] (sq : CommSq (ofOverMap ψ) a b f) :
    AlgebraicGeometry.FormallySmooth ψ.left :=
  sorry

/-- A commutative square of schemes with étale surjective vertical arrows and
formally smooth top arrow witnesses that the bottom morphism of algebraic spaces
is formally smooth. -/
theorem of_surjectiveEtaleSchemeSquare {S : Scheme.{u}} {U V : Over S}
    {X Y : AlgebraicSpace S} {ψ : U ⟶ V} {a : ofOver U ⟶ X} {b : ofOver V ⟶ Y}
    {f : X ⟶ Y} [AlgebraicSpace.Etale a] [AlgebraicSpace.Etale b]
    [AlgebraicSpace.Surjective a] [AlgebraicSpace.Surjective b]
    [AlgebraicGeometry.FormallySmooth ψ.left]
    (sq : CommSq (ofOverMap ψ) a b f) : FormallySmooth f :=
  sorry

/-- On a commutative square with étale surjective vertical arrows from schemes,
space-level formal smoothness of the bottom arrow is equivalent to
scheme-level formal smoothness of the top arrow. -/
theorem iff_of_surjectiveEtaleSchemeSquare {S : Scheme.{u}} {U V : Over S}
    {X Y : AlgebraicSpace S} {ψ : U ⟶ V} {a : ofOver U ⟶ X} {b : ofOver V ⟶ Y}
    {f : X ⟶ Y} [AlgebraicSpace.Etale a] [AlgebraicSpace.Etale b]
    [AlgebraicSpace.Surjective a] [AlgebraicSpace.Surjective b]
    (sq : CommSq (ofOverMap ψ) a b f) :
    FormallySmooth f ↔ AlgebraicGeometry.FormallySmooth ψ.left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FormallySmooth
