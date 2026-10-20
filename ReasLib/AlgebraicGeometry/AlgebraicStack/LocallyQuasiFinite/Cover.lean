module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiDM.Cover

/-!
# Covering characterizations of locally quasi-finite morphisms of algebraic stacks

A morphism of algebraic stacks is locally quasi-finite precisely when it is
quasi-DM and locally quasi-finite algebraic-space maps into 2-fibre products
remain locally quasi-finite after composing to the test space, equivalently
when those 2-fibre products admit a surjective, flat, locally of finite
presentation, locally quasi-finite algebraic-space cover whose composite to
the test space is locally quasi-finite.
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

namespace forallSpaceMaps

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
  hf V g U h inferInstance

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

namespace existsCoverOver

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
  hp

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

namespace existsCoverOnPullbacks

/-- Under `existsCoverOnPullbacks f`, every 2-fibre product of `f` against an
algebraic space over the target admits a locally quasi-finite flat
algebraic-space cover whose composite to that space is locally
quasi-finite. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : existsCoverOnPullbacks f) (V : AlgebraicSpace S)
    (g : V.toGroupoids ⟶ Y) :
    existsCoverOver (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  hf V g

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

namespace existsCoverOverFppf

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
  hf

end existsCoverOverFppf

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)

/-- For a morphism `f : X ⟶ Y` of algebraic stacks, the
following are equivalent: `LocallyQuasiFinite f`; `QuasiDM f` and
`forallSpaceMaps f`; `existsCoverOnPullbacks f`; and `existsCoverOverFppf f`. -/
@[stacks 06UF]
theorem tfae :
    List.TFAE [LocallyQuasiFinite f, QuasiDM f ∧ forallSpaceMaps f,
      existsCoverOnPullbacks f, existsCoverOverFppf f] :=
  sorry

/-- A morphism of algebraic stacks is locally quasi-finite iff it is quasi-DM
and locally quasi-finite algebraic-space maps into 2-fibre products remain
locally quasi-finite after composing to the test space. -/
theorem iff_forallSpaceMaps :
    LocallyQuasiFinite f ↔ QuasiDM f ∧ forallSpaceMaps f :=
  (tfae f).out 0 1

/-- A morphism of algebraic stacks is locally quasi-finite iff every
algebraic-space test of the target has a locally quasi-finite flat
algebraic-space cover of the 2-fibre product whose composite to the test
space is locally quasi-finite. -/
theorem iff_existsCoverOnPullbacks :
    LocallyQuasiFinite f ↔ existsCoverOnPullbacks f :=
  (tfae f).out 0 2

/-- A morphism of algebraic stacks is locally quasi-finite iff some fppf
algebraic-space cover of the target has a locally quasi-finite flat
algebraic-space cover of the 2-fibre product whose composite to that cover
is locally quasi-finite. -/
theorem iff_existsCoverOverFppf :
    LocallyQuasiFinite f ↔ existsCoverOverFppf f :=
  (tfae f).out 0 3

end AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite
