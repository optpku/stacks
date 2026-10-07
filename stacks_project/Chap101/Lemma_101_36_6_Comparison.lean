module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap94.«94_8_2_1_FullyFaithful»
public import stacks_project.Chap94.Definition_94_12_2_Etale
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap100.Lemma_100_11_1_Flat
public import stacks_project.Chap101.Lemma_101_36_4_Unramified

/-!
# Étale-on-pullbacks and fppf-étale tests for unramified morphisms

A morphism of algebraic stacks may be tested for unramifiedness on étale
algebraic-space morphisms into 2-fibre products against arbitrary algebraic
spaces over the target, or on a single fppf algebraic-space cover of the
target together with a surjective étale unramified comparison.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Unramified

/-- The morphism of algebraic spaces recovered from the composite of a
comparison `p` into `TwoFibreProduct.apex f g` with the second projection. -/
def evalSnd {S : Scheme.{u}} {X Y : GroupoidsOver S} {V : AlgebraicSpace S}
    (f : X ⟶ Y) (g : V.toGroupoids ⟶ Y) {U : AlgebraicSpace S}
    (p : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g) :
    U ⟶ V :=
  AlgebraicSpace.toGroupoids.eval
    (p ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)

/-- `evalSnd f g p` is `toGroupoids.eval` of `p ≫ TwoFibreProduct.snd f g`. -/
theorem evalSnd_eq {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {V : AlgebraicSpace S} (f : X ⟶ Y) (g : V.toGroupoids ⟶ Y)
    {U : AlgebraicSpace S}
    (p : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g) :
    evalSnd f g p =
      AlgebraicSpace.toGroupoids.eval
        (p ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- For every algebraic space `V` and morphism `g : V.toGroupoids ⟶ Y`, every
étale morphism from an algebraic space into `TwoFibreProduct.apex f g`
(informally `X ×_Y V`) recovers an unramified morphism of algebraic spaces
to `V`. -/
def forallEtaleOnPullbacks {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  ∀ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y) (U : AlgebraicSpace S)
    (p : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
    Groupoids.Hom.Etale p → AlgebraicSpace.Unramified (evalSnd f g p)

/-- `forallEtaleOnPullbacks f` unpacks to unramifiedness of the recovered
morphism of algebraic spaces for every étale algebraic-space comparison into
a 2-fibre product of `f` against an algebraic space over the target. -/
theorem forallEtaleOnPullbacks.iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    forallEtaleOnPullbacks f ↔
      ∀ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y) (U : AlgebraicSpace S)
        (p : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
        Groupoids.Hom.Etale p → AlgebraicSpace.Unramified (evalSnd f g p) :=
  sorry

namespace forallEtaleOnPullbacks

/-- Unramifiedness of every recovered étale algebraic-space comparison into a
2-fibre product of `f` against an algebraic space over the target witnesses
`forallEtaleOnPullbacks`. -/
theorem of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (h : ∀ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y)
      (U : AlgebraicSpace S)
      (p : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
      Groupoids.Hom.Etale p → AlgebraicSpace.Unramified (evalSnd f g p)) :
    forallEtaleOnPullbacks f :=
  sorry

/-- Under `forallEtaleOnPullbacks f`, an étale algebraic-space comparison into
a 2-fibre product of `f` against an algebraic space over the target recovers
an unramified morphism of algebraic spaces. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : forallEtaleOnPullbacks f) (V : AlgebraicSpace S)
    (g : V.toGroupoids ⟶ Y) (U : AlgebraicSpace S)
    (p : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)
    (hp : Groupoids.Hom.Etale p) :
    AlgebraicSpace.Unramified (evalSnd f g p) :=
  sorry

end forallEtaleOnPullbacks

/-- There exist algebraic spaces `W`, `T`, a surjective, flat, locally of
finite presentation morphism `g : W.toGroupoids ⟶ Y`, and a surjective étale
morphism `p` from `T` to `TwoFibreProduct.apex f g` (informally `X ×_Y W`)
such that the recovered morphism of algebraic spaces `T ⟶ W` is unramified. -/
def existsFppfEtaleSquare {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  ∃ (W T : AlgebraicSpace S) (g : W.toGroupoids ⟶ Y)
    (p : T.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
    Groupoids.Hom.Surjective g ∧ Groupoids.Hom.Flat g ∧
      Groupoids.Hom.LocallyOfFinitePresentation g ∧
      Groupoids.Hom.Surjective p ∧ Groupoids.Hom.Etale p ∧
      AlgebraicSpace.Unramified (evalSnd f g p)

/-- `existsFppfEtaleSquare f` unpacks to one fppf algebraic-space cover of the
target together with a surjective étale algebraic-space comparison into the
2-fibre product whose recovered morphism of algebraic spaces is unramified. -/
theorem existsFppfEtaleSquare.iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    existsFppfEtaleSquare f ↔
      ∃ (W T : AlgebraicSpace S) (g : W.toGroupoids ⟶ Y)
        (p : T.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
        Groupoids.Hom.Surjective g ∧ Groupoids.Hom.Flat g ∧
          Groupoids.Hom.LocallyOfFinitePresentation g ∧
          Groupoids.Hom.Surjective p ∧ Groupoids.Hom.Etale p ∧
          AlgebraicSpace.Unramified (evalSnd f g p) :=
  sorry

namespace existsFppfEtaleSquare

/-- An fppf algebraic-space cover of the target together with a surjective
étale algebraic-space comparison into the 2-fibre product whose recovered
morphism of algebraic spaces is unramified witnesses `existsFppfEtaleSquare`. -/
theorem of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    {W T : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    (p : T.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)
    (h_surjective : Groupoids.Hom.Surjective g)
    (h_flat : Groupoids.Hom.Flat g)
    (h_locallyOfFinitePresentation : Groupoids.Hom.LocallyOfFinitePresentation g)
    (h_p_surjective : Groupoids.Hom.Surjective p)
    (h_p_etale : Groupoids.Hom.Etale p)
    (h_unramified : AlgebraicSpace.Unramified (evalSnd f g p)) :
    existsFppfEtaleSquare f :=
  sorry

/-- `existsFppfEtaleSquare f` supplies an fppf algebraic-space cover of the
target and a surjective étale algebraic-space comparison into the 2-fibre
product whose recovered morphism of algebraic spaces is unramified. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : existsFppfEtaleSquare f) :
    ∃ (W T : AlgebraicSpace S) (g : W.toGroupoids ⟶ Y)
      (p : T.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
      Groupoids.Hom.Surjective g ∧ Groupoids.Hom.Flat g ∧
        Groupoids.Hom.LocallyOfFinitePresentation g ∧
        Groupoids.Hom.Surjective p ∧ Groupoids.Hom.Etale p ∧
        AlgebraicSpace.Unramified (evalSnd f g p) :=
  sorry

end existsFppfEtaleSquare

end AlgebraicGeometry.AlgebraicStack.Unramified
