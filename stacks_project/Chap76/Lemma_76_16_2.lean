module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyEtale
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap76.Lemma_76_16_4_FormallyEtale

/-!
# Formal étaleness via étale scheme squares

A morphism of algebraic spaces is formally étale if and only if every
commutative square with scheme vertices and étale vertical arrows has
formally étale top arrow, and if and only if some such square with
surjective vertical arrows does.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FormallyEtale

/-- Every commutative square of schemes over `f` with étale vertical arrows has
formally étale top arrow in the sense of `AlgebraicGeometry.FormallyEtale`. -/
def forallEtaleSchemeSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∀ {U V : Over S} (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (ψ : U ⟶ V),
    AlgebraicSpace.Etale a → AlgebraicSpace.Etale b →
      CommSq (ofOverMap ψ) a b f → AlgebraicGeometry.FormallyEtale ψ.left

/-- Unfolding of `forallEtaleSchemeSquare`. -/
theorem forallEtaleSchemeSquare_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    forallEtaleSchemeSquare f ↔
      ∀ {U V : Over S} (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (ψ : U ⟶ V),
        AlgebraicSpace.Etale a → AlgebraicSpace.Etale b →
          CommSq (ofOverMap ψ) a b f →
            AlgebraicGeometry.FormallyEtale ψ.left :=
  sorry

/-- There is a commutative square of schemes over `f` with étale surjective
vertical arrows and formally étale top arrow. -/
def existsSurjectiveEtaleSchemeSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (ψ : U ⟶ V),
    AlgebraicSpace.Etale a ∧ AlgebraicSpace.Etale b ∧
      AlgebraicSpace.Surjective a ∧ AlgebraicSpace.Surjective b ∧
        CommSq (ofOverMap ψ) a b f ∧ AlgebraicGeometry.FormallyEtale ψ.left

/-- Unfolding of `existsSurjectiveEtaleSchemeSquare`. -/
theorem existsSurjectiveEtaleSchemeSquare_iff {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    existsSurjectiveEtaleSchemeSquare f ↔
      ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (ψ : U ⟶ V),
        AlgebraicSpace.Etale a ∧ AlgebraicSpace.Etale b ∧
          AlgebraicSpace.Surjective a ∧ AlgebraicSpace.Surjective b ∧
            CommSq (ofOverMap ψ) a b f ∧
              AlgebraicGeometry.FormallyEtale ψ.left :=
  sorry

/-- Lemma 76.16.2 (1): A morphism of algebraic spaces over `S` is formally étale
if and only if every commutative square with scheme vertices and étale vertical
arrows has formally étale top arrow. -/
@[stacks 04GD]
theorem iff_forallEtaleSchemeSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : FormallyEtale f ↔ forallEtaleSchemeSquare f :=
  sorry

/-- Lemma 76.16.2 (2): A morphism of algebraic spaces over `S` is formally étale
if and only if some commutative square with scheme vertices and étale surjective
vertical arrows has formally étale top arrow. -/
@[stacks 04GD]
theorem iff_existsSurjectiveEtaleSchemeSquare {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    FormallyEtale f ↔ existsSurjectiveEtaleSchemeSquare f :=
  sorry

/-- In a commutative square of schemes over a formally étale morphism of
algebraic spaces, étale vertical arrows make the top arrow formally étale. -/
theorem of_etale_commSq {S : Scheme.{u}} {U V : Over S} {X Y : AlgebraicSpace S}
    {ψ : U ⟶ V} {a : ofOver U ⟶ X} {b : ofOver V ⟶ Y} {f : X ⟶ Y}
    [AlgebraicSpace.Etale a] [AlgebraicSpace.Etale b] [FormallyEtale f]
    (sq : CommSq (ofOverMap ψ) a b f) :
    AlgebraicGeometry.FormallyEtale ψ.left :=
  sorry

/-- A commutative square of schemes with étale surjective vertical arrows and
formally étale top arrow witnesses that the bottom morphism of algebraic spaces
is formally étale. -/
theorem of_surjective_etale_commSq {S : Scheme.{u}} {U V : Over S}
    {X Y : AlgebraicSpace S} {ψ : U ⟶ V} {a : ofOver U ⟶ X} {b : ofOver V ⟶ Y}
    {f : X ⟶ Y} [AlgebraicSpace.Etale a] [AlgebraicSpace.Etale b]
    [AlgebraicSpace.Surjective a] [AlgebraicSpace.Surjective b]
    [AlgebraicGeometry.FormallyEtale ψ.left]
    (sq : CommSq (ofOverMap ψ) a b f) : FormallyEtale f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FormallyEtale
