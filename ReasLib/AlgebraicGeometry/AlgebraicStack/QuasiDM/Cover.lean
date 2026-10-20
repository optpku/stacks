/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation

/-!
# Algebraic-space covering criteria for quasi-DM morphisms

A morphism of algebraic stacks is quasi-DM precisely when its pullbacks along
algebraic spaces admit surjective, flat, locally of finite presentation,
locally quasi-finite algebraic-space covers. Equivalently, such a cover exists
after one fppf algebraic-space cover of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- There exists an algebraic space `W` over `S` and a surjective, flat,
locally of finite presentation, locally quasi-finite morphism
`W.toGroupoids ⟶ X`. -/
def existsLocallyQuasiFiniteFlatSpaceCover {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] : Prop :=
  ∃ (W : AlgebraicSpace S) (h : W.toGroupoids ⟶ X),
    Groupoids.Hom.Surjective h ∧ Groupoids.Hom.Flat h ∧
      Groupoids.Hom.LocallyOfFinitePresentation h ∧
      Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) h

namespace existsLocallyQuasiFiniteFlatSpaceCover

/-- `existsLocallyQuasiFiniteFlatSpaceCover X` supplies a surjective, flat,
locally of finite presentation, locally quasi-finite morphism from an
algebraic space over `S`. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (hX : existsLocallyQuasiFiniteFlatSpaceCover X) :
    ∃ (W : AlgebraicSpace S) (h : W.toGroupoids ⟶ X),
      Groupoids.Hom.Surjective h ∧ Groupoids.Hom.Flat h ∧
        Groupoids.Hom.LocallyOfFinitePresentation h ∧
        Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) h :=
  hX

end existsLocallyQuasiFiniteFlatSpaceCover

namespace QuasiDM

/-- For every algebraic space `V` and morphism `g : V.toGroupoids ⟶ Y`, the
2-fibre product `TwoFibreProduct.apex f g` (informally `X ×_Y V`) admits a
surjective, flat, locally of finite presentation, locally quasi-finite
morphism from an algebraic space. -/
def existsCoverOnPullbacks {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  ∀ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y),
    existsLocallyQuasiFiniteFlatSpaceCover
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)

namespace existsCoverOnPullbacks

/-- Under `existsCoverOnPullbacks f`, every 2-fibre product of `f` against an
algebraic space over the target admits a locally quasi-finite flat
algebraic-space cover. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : existsCoverOnPullbacks f) (V : AlgebraicSpace S)
    (g : V.toGroupoids ⟶ Y) :
    existsLocallyQuasiFiniteFlatSpaceCover
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g) :=
  hf V g

end existsCoverOnPullbacks

/-- There exist algebraic spaces `U`, `V` and a surjective, flat, locally of
finite presentation morphism `g : V.toGroupoids ⟶ Y` such that
`TwoFibreProduct.apex f g` (informally `X ×_Y V`) admits a surjective, flat,
locally of finite presentation, locally quasi-finite morphism from `U`. -/
def existsCoverOverFppf {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  ∃ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y),
    Groupoids.Hom.Surjective g ∧ Groupoids.Hom.Flat g ∧
      Groupoids.Hom.LocallyOfFinitePresentation g ∧
      existsLocallyQuasiFiniteFlatSpaceCover
        (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)

namespace existsCoverOverFppf

/-- `existsCoverOverFppf f` supplies an fppf algebraic-space cover of the
target and a locally quasi-finite flat algebraic-space cover of the
corresponding 2-fibre product. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : existsCoverOverFppf f) :
    ∃ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y),
      Groupoids.Hom.Surjective g ∧ Groupoids.Hom.Flat g ∧
        Groupoids.Hom.LocallyOfFinitePresentation g ∧
        existsLocallyQuasiFiniteFlatSpaceCover
          (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g) :=
  hf

end existsCoverOverFppf

/-- A morphism of algebraic stacks is quasi-DM if and only if every
algebraic-space test of its target yields a 2-fibre product admitting a
surjective, flat, locally of finite presentation, locally quasi-finite
algebraic-space cover. -/
theorem iff_existsCoverOnPullbacks {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    QuasiDM f ↔ existsCoverOnPullbacks f :=
  sorry

/-- A morphism of algebraic stacks is quasi-DM if and only if some
surjective, flat, locally of finite presentation algebraic-space cover of
its target yields a 2-fibre product admitting a surjective, flat, locally
of finite presentation, locally quasi-finite algebraic-space cover. -/
theorem iff_existsCoverOverFppf {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    QuasiDM f ↔ existsCoverOverFppf f :=
  sorry

end QuasiDM

end AlgebraicGeometry.AlgebraicStack
