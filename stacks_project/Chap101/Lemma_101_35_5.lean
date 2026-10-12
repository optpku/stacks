/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap94.Lemma_94_14_3_Pullback
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap100.Lemma_100_11_1_Flat
public import stacks_project.Chap101.Lemma_101_36_4_Etale

/-!
# Characterizations of étale morphisms of algebraic stacks

A morphism of algebraic stacks is étale if and only if it is DM and every
étale morphism from an algebraic space into a 2-fibre product against an
arbitrary algebraic-space test remains étale after composing to that test
space, equivalently if and only if some fppf algebraic-space cover of the
target admits a surjective étale algebraic-space atlas whose composite is
étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Etale

/-- The morphism of algebraic spaces `U ⟶ V` recovered from a comparison
`p : U.toGroupoids ⟶ TwoFibreProduct.apex f g` into the 2-fibre product
`V ×_Y X` by composing with `TwoFibreProduct.snd f g` and evaluating. -/
def spaceMap {S : Scheme.{u}} {X Y : GroupoidsOver S} {V : AlgebraicSpace S}
    (f : X ⟶ Y) (g : V.toGroupoids ⟶ Y) {U : AlgebraicSpace S}
    (p : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g) :
    U ⟶ V :=
  AlgebraicSpace.toGroupoids.eval
    (p ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)

/-- `spaceMap f g p` is the algebraic-space morphism recovered from
`p ≫ TwoFibreProduct.snd f g`. -/
theorem spaceMap_def {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {V : AlgebraicSpace S} (f : X ⟶ Y) (g : V.toGroupoids ⟶ Y)
    {U : AlgebraicSpace S}
    (p : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g) :
    spaceMap f g p =
      AlgebraicSpace.toGroupoids.eval
        (p ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- For every algebraic space `V` and morphism `g : V.toGroupoids ⟶ Y`, every
étale morphism from an algebraic space into `TwoFibreProduct.apex f g`
(informally `V ×_Y X`) remains étale after composing to `V`. -/
def forallAlgebraicSpace {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  ∀ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y) (U : AlgebraicSpace S)
    (p : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
    Groupoids.Hom.Etale p → AlgebraicSpace.Etale (spaceMap f g p)

/-- `forallAlgebraicSpace f` unpacks to the universal algebraic-space test:
étale comparisons into every 2-fibre product of `f` against an algebraic space
over the target remain étale after composing to that space. -/
theorem forallAlgebraicSpace.iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    forallAlgebraicSpace f ↔
      ∀ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y) (U : AlgebraicSpace S)
        (p : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
        Groupoids.Hom.Etale p → AlgebraicSpace.Etale (spaceMap f g p) :=
  sorry

namespace forallAlgebraicSpace

/-- The universal algebraic-space étale test witnesses
`forallAlgebraicSpace`. -/
theorem of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (H : ∀ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y)
      (U : AlgebraicSpace S)
      (p : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
      Groupoids.Hom.Etale p → AlgebraicSpace.Etale (spaceMap f g p)) :
    forallAlgebraicSpace f :=
  sorry

/-- Under `forallAlgebraicSpace f`, an étale morphism from an algebraic space
into a 2-fibre product of `f` against an algebraic space over the target
remains étale after composing to that space. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : forallAlgebraicSpace f) (V : AlgebraicSpace S)
    (g : V.toGroupoids ⟶ Y) (U : AlgebraicSpace S)
    (p : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)
    (hp : Groupoids.Hom.Etale p) :
    AlgebraicSpace.Etale (spaceMap f g p) :=
  sorry

end forallAlgebraicSpace

/-- There exist algebraic spaces `W`, `T`, an fppf morphism
`g : W.toGroupoids ⟶ Y`, and a surjective étale morphism
`p : T.toGroupoids ⟶ TwoFibreProduct.apex f g` (informally `T ⟶ W ×_Y X`)
such that `T ⟶ W` is étale. -/
def existsFppfSquare {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  ∃ (W T : AlgebraicSpace S) (g : W.toGroupoids ⟶ Y)
    (p : T.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
    Groupoids.Hom.Surjective g ∧ Groupoids.Hom.LocallyOfFinitePresentation g ∧
      Groupoids.Hom.Flat g ∧ Groupoids.Hom.Etale p ∧
        Groupoids.Hom.Surjective p ∧ AlgebraicSpace.Etale (spaceMap f g p)

/-- `existsFppfSquare f` unpacks to an fppf algebraic-space cover of the
target together with a surjective étale algebraic-space atlas of the
corresponding 2-fibre product whose composite to the cover is étale. -/
theorem existsFppfSquare.iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    existsFppfSquare f ↔
      ∃ (W T : AlgebraicSpace S) (g : W.toGroupoids ⟶ Y)
        (p : T.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
        Groupoids.Hom.Surjective g ∧
          Groupoids.Hom.LocallyOfFinitePresentation g ∧
            Groupoids.Hom.Flat g ∧ Groupoids.Hom.Etale p ∧
              Groupoids.Hom.Surjective p ∧
                AlgebraicSpace.Etale (spaceMap f g p) :=
  sorry

namespace existsFppfSquare

/-- An fppf algebraic-space cover of the target together with a surjective
étale algebraic-space atlas of the 2-fibre product whose composite is étale
witnesses `existsFppfSquare`. -/
theorem of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    {W T : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    (p : T.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)
    (h_surjective : Groupoids.Hom.Surjective g)
    (h_locallyOfFinitePresentation : Groupoids.Hom.LocallyOfFinitePresentation g)
    (h_flat : Groupoids.Hom.Flat g) (h_p_etale : Groupoids.Hom.Etale p)
    (h_p_surjective : Groupoids.Hom.Surjective p)
    (h_etale : AlgebraicSpace.Etale (spaceMap f g p)) :
    existsFppfSquare f :=
  sorry

/-- `existsFppfSquare f` supplies an fppf algebraic-space cover of the target
and a surjective étale algebraic-space atlas of the corresponding 2-fibre
product whose composite to the cover is étale. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : existsFppfSquare f) :
    ∃ (W T : AlgebraicSpace S) (g : W.toGroupoids ⟶ Y)
      (p : T.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
      Groupoids.Hom.Surjective g ∧
        Groupoids.Hom.LocallyOfFinitePresentation g ∧
          Groupoids.Hom.Flat g ∧ Groupoids.Hom.Etale p ∧
            Groupoids.Hom.Surjective p ∧
              AlgebraicSpace.Etale (spaceMap f g p) :=
  sorry

end existsFppfSquare

/-- Lemma 101.35.5: Let `f : X ⟶ Y` be a morphism of algebraic stacks. The
following are equivalent: `Etale f`; `DM f` and, for any algebraic space `V`
with morphism `g : V.toGroupoids ⟶ Y` and any étale morphism
`p : U.toGroupoids ⟶ TwoFibreProduct.apex f g` from an algebraic space `U`,
the recovered morphism `spaceMap f g p : U ⟶ V` is étale; and there exist
algebraic spaces `W`, `T`, a surjective, locally of finite presentation, and
flat morphism `g : W.toGroupoids ⟶ Y`, and a surjective étale morphism
`p : T.toGroupoids ⟶ TwoFibreProduct.apex f g` such that
`spaceMap f g p : T ⟶ W` is étale.

Stacks writes `V ×_Y X` and `W ×_Y X`; the Lean objects are
`TwoFibreProduct.apex f g`. Stacks writes `U ⟶ V` and `T ⟶ W`; the Lean
morphisms are `spaceMap f g p`. -/
@[stacks 0CIQ]
theorem tfae {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    List.TFAE
      [Etale f,
        DM f ∧
          ∀ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y)
            (U : AlgebraicSpace S)
            (p : U.toGroupoids ⟶
              TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
            Groupoids.Hom.Etale p → AlgebraicSpace.Etale (spaceMap f g p),
        ∃ (W T : AlgebraicSpace S) (g : W.toGroupoids ⟶ Y)
          (p : T.toGroupoids ⟶
            TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
          Groupoids.Hom.Surjective g ∧
            Groupoids.Hom.LocallyOfFinitePresentation g ∧
              Groupoids.Hom.Flat g ∧ Groupoids.Hom.Etale p ∧
                Groupoids.Hom.Surjective p ∧
                  AlgebraicSpace.Etale (spaceMap f g p)] :=
  sorry

/-- A morphism of algebraic stacks is étale if and only if it is DM and every
étale algebraic-space comparison into a 2-fibre product against an algebraic
space over the target remains étale after composing to that space. -/
theorem iff_forallAlgebraicSpace {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Etale f ↔ DM f ∧ forallAlgebraicSpace f :=
  sorry

/-- A morphism of algebraic stacks is étale if and only if some fppf
algebraic-space cover of the target admits a surjective étale algebraic-space
atlas whose composite to the cover is étale. -/
theorem iff_existsFppfSquare {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Etale f ↔ existsFppfSquare f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Etale
