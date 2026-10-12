/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_23_2_LocallyQuasiFinite
public import stacks_project.Chap101.Lemma_101_23_6_Covering

/-!
# Covering characterizations of locally quasi-finite morphisms of algebraic stacks

A morphism of algebraic stacks is locally quasi-finite precisely when it is
quasi-DM and locally quasi-finite algebraic-space maps into 2-fibre products
remain locally quasi-finite after composing to the test space, equivalently
when those 2-fibre products admit a surjective, flat, locally of finite
presentation, locally quasi-finite algebraic-space cover whose composite to
the test space is locally quasi-finite. This module records the covering
predicates; the source-facing equivalences live in the labeled item file.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite

/-- For every algebraic space `V` and morphism `g : V.toGroupoids ⟶ Y`, every
locally quasi-finite morphism from an algebraic space to
`TwoFibreProduct.apex f g` (informally `X ×_Y V`) remains locally
quasi-finite after composing with `TwoFibreProduct.snd f g`. -/
def forallSpaceMaps {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  ∀ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y) (U : AlgebraicSpace S)
    (h : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
    LocallyQuasiFinite h →
      LocallyQuasiFinite (h ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)

/-- `forallSpaceMaps f` unpacks to preservation of locally quasi-finite
algebraic-space maps into every 2-fibre product of `f` against an algebraic
space over the target. -/
theorem forallSpaceMaps.iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    forallSpaceMaps f ↔
      ∀ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y) (U : AlgebraicSpace S)
        (h : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
        LocallyQuasiFinite h →
          LocallyQuasiFinite
            (h ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

namespace forallSpaceMaps

/-- Preservation of locally quasi-finite algebraic-space maps into every
2-fibre product of `f` against an algebraic space over the target witnesses
`forallSpaceMaps`. -/
theorem of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (H : ∀ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y)
      (U : AlgebraicSpace S)
      (h : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
      LocallyQuasiFinite h →
        LocallyQuasiFinite
          (h ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)) :
    forallSpaceMaps f :=
  sorry

/-- Under `forallSpaceMaps f`, a locally quasi-finite morphism from an
algebraic space to a 2-fibre product of `f` against an algebraic space over
the target remains locally quasi-finite after composing to that space. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : forallSpaceMaps f) (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y)
    (U : AlgebraicSpace S)
    (h : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)
    [LocallyQuasiFinite h] :
    LocallyQuasiFinite (h ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end forallSpaceMaps

/-- There exists an algebraic space `U` and a surjective, flat, locally of
finite presentation, locally quasi-finite morphism `h : U.toGroupoids ⟶ X`
such that the composite `h ≫ p` is locally quasi-finite. -/
def existsCoverOver {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {V : AlgebraicSpace S} (p : X ⟶ V.toGroupoids) : Prop :=
  ∃ (U : AlgebraicSpace S) (h : U.toGroupoids ⟶ X),
    Groupoids.Hom.Surjective h ∧ Groupoids.Hom.Flat h ∧
      Groupoids.Hom.LocallyOfFinitePresentation h ∧
      Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) h ∧
      LocallyQuasiFinite (h ≫ p)

/-- `existsCoverOver p` unpacks to a surjective, flat, locally of finite
presentation, locally quasi-finite morphism from an algebraic space whose
composite with `p` is locally quasi-finite. -/
theorem existsCoverOver.iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {V : AlgebraicSpace S} (p : X ⟶ V.toGroupoids) :
    existsCoverOver p ↔
      ∃ (U : AlgebraicSpace S) (h : U.toGroupoids ⟶ X),
        Groupoids.Hom.Surjective h ∧ Groupoids.Hom.Flat h ∧
          Groupoids.Hom.LocallyOfFinitePresentation h ∧
          Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) h ∧
          LocallyQuasiFinite (h ≫ p) :=
  sorry

namespace existsCoverOver

/-- A surjective, flat, locally of finite presentation, locally quasi-finite
morphism from an algebraic space whose composite with `p` is locally
quasi-finite witnesses `existsCoverOver`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {V : AlgebraicSpace S} {p : X ⟶ V.toGroupoids} {U : AlgebraicSpace S}
    (h : U.toGroupoids ⟶ X) [Groupoids.Hom.Surjective h]
    [Groupoids.Hom.Flat h] [Groupoids.Hom.LocallyOfFinitePresentation h]
    (h_locallyQuasiFinite :
      Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) h)
    [LocallyQuasiFinite (h ≫ p)] : existsCoverOver p :=
  sorry

/-- `existsCoverOver p` supplies a surjective, flat, locally of finite
presentation, locally quasi-finite morphism from an algebraic space whose
composite with `p` is locally quasi-finite. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {V : AlgebraicSpace S} {p : X ⟶ V.toGroupoids} (hp : existsCoverOver p) :
    ∃ (U : AlgebraicSpace S) (h : U.toGroupoids ⟶ X),
      Groupoids.Hom.Surjective h ∧ Groupoids.Hom.Flat h ∧
        Groupoids.Hom.LocallyOfFinitePresentation h ∧
        Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) h ∧
        LocallyQuasiFinite (h ≫ p) :=
  sorry

/-- Dropping the locally quasi-finite condition on the composite recovers a
locally quasi-finite flat algebraic-space cover of the source. -/
theorem to_existsLocallyQuasiFiniteFlatSpaceCover {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] {V : AlgebraicSpace S}
    {p : X ⟶ V.toGroupoids} (hp : existsCoverOver p) :
    existsLocallyQuasiFiniteFlatSpaceCover X :=
  sorry

end existsCoverOver

/-- For every algebraic space `V` and morphism `g : V.toGroupoids ⟶ Y`, the
2-fibre product `TwoFibreProduct.apex f g` (informally `X ×_Y V`) admits a
surjective, flat, locally of finite presentation, locally quasi-finite
morphism from an algebraic space whose composite with
`TwoFibreProduct.snd f g` is locally quasi-finite. -/
def existsCoverOnPullbacks {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  ∀ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y),
    existsCoverOver (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)

/-- `existsCoverOnPullbacks f` unpacks to a locally quasi-finite flat
algebraic-space cover of every 2-fibre product of `f` against an algebraic
space over the target, with locally quasi-finite composite to that space. -/
theorem existsCoverOnPullbacks.iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    existsCoverOnPullbacks f ↔
      ∀ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y),
        existsCoverOver (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

namespace existsCoverOnPullbacks

/-- A locally quasi-finite flat algebraic-space cover of every 2-fibre product
of `f` against an algebraic space over the target, with locally quasi-finite
composite to that space, witnesses `existsCoverOnPullbacks`. -/
theorem of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (h : ∀ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y),
      existsCoverOver (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)) :
    existsCoverOnPullbacks f :=
  sorry

/-- Under `existsCoverOnPullbacks f`, every 2-fibre product of `f` against an
algebraic space over the target admits a locally quasi-finite flat
algebraic-space cover whose composite to that space is locally
quasi-finite. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : existsCoverOnPullbacks f) (V : AlgebraicSpace S)
    (g : V.toGroupoids ⟶ Y) :
    existsCoverOver (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- Dropping the locally quasi-finite condition on composites `U ⟶ V`
recovers the quasi-DM covering criterion on every algebraic-space test. -/
theorem to_quasiDM {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (h : existsCoverOnPullbacks f) : QuasiDM.existsCoverOnPullbacks f :=
  sorry

end existsCoverOnPullbacks

/-- There exist algebraic spaces `U`, `V` and a surjective, flat, locally of
finite presentation morphism `g : V.toGroupoids ⟶ Y` such that
`TwoFibreProduct.apex f g` (informally `X ×_Y V`) admits a surjective, flat,
locally of finite presentation, locally quasi-finite morphism from `U` whose
composite with `TwoFibreProduct.snd f g` is locally quasi-finite. -/
def existsCoverOverFppf {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  ∃ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y),
    Groupoids.Hom.Surjective g ∧ Groupoids.Hom.Flat g ∧
      Groupoids.Hom.LocallyOfFinitePresentation g ∧
      existsCoverOver (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)

/-- `existsCoverOverFppf f` unpacks to one fppf algebraic-space cover of the
target together with a locally quasi-finite flat algebraic-space cover of the
corresponding 2-fibre product whose composite to the cover is locally
quasi-finite. -/
theorem existsCoverOverFppf.iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    existsCoverOverFppf f ↔
      ∃ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y),
        Groupoids.Hom.Surjective g ∧ Groupoids.Hom.Flat g ∧
          Groupoids.Hom.LocallyOfFinitePresentation g ∧
          existsCoverOver (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

namespace existsCoverOverFppf

/-- An fppf algebraic-space cover of the target together with a locally
quasi-finite flat algebraic-space cover of the 2-fibre product whose
composite to the cover is locally quasi-finite witnesses
`existsCoverOverFppf`. -/
theorem of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    {V : AlgebraicSpace S} (g : V.toGroupoids ⟶ Y)
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    (h : existsCoverOver (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)) :
    existsCoverOverFppf f :=
  sorry

/-- `existsCoverOverFppf f` supplies an fppf algebraic-space cover of the
target and a locally quasi-finite flat algebraic-space cover of the
corresponding 2-fibre product whose composite to the cover is locally
quasi-finite. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : existsCoverOverFppf f) :
    ∃ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y),
      Groupoids.Hom.Surjective g ∧ Groupoids.Hom.Flat g ∧
        Groupoids.Hom.LocallyOfFinitePresentation g ∧
        existsCoverOver (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- Dropping the locally quasi-finite condition on composites `U ⟶ V`
recovers the quasi-DM fppf covering criterion. -/
theorem to_quasiDM {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (h : existsCoverOverFppf f) : QuasiDM.existsCoverOverFppf f :=
  sorry

end existsCoverOverFppf

/-- The covering criterion on every algebraic-space test implies the existence
of one fppf algebraic-space cover of the target with a locally quasi-finite
flat algebraic-space cover of the 2-fibre product whose composite is locally
quasi-finite. -/
theorem existsCoverOverFppf_of_existsCoverOnPullbacks {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (h : existsCoverOnPullbacks f) : existsCoverOverFppf f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite
