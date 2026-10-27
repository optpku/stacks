/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Closed
public import ReasLib.AlgebraicGeometry.GroupoidsOver.MorphismProperty

/-!
# Local tests for universally closed morphisms of algebraic stacks

Universally closed morphisms of algebraic stacks may be tested by closed
projections after scheme-valued and affine base change, and by a surjective
smooth algebraic-space atlas of the target along which the base change is
universally closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace Closed

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)

/-- The projection of every scheme-valued base change of `f` is a closed map on
points. -/
def forallScheme : Prop :=
  ∀ {Z : Over S} {P : GroupoidsOver S} [AlgebraicStack P]
    {g : GroupoidsOver.slice Z ⟶ Y} {fst : P ⟶ X}
    {snd : P ⟶ GroupoidsOver.slice Z} (iso : fst ≫ f ≅ snd ≫ g),
    (CategoryTheory.Bicategory.PseudoPullbackCone.mk f g P fst snd iso).IsBilimit → Closed snd

/-- `forallScheme f` means every scheme-valued 2-fibre-product projection of `f`
is a closed morphism. -/
theorem forallScheme_iff : forallScheme f ↔
    ∀ (Z : Over S) (P : GroupoidsOver S) [AlgebraicStack P]
      (g : GroupoidsOver.slice Z ⟶ Y) (fst : P ⟶ X)
      (snd : P ⟶ GroupoidsOver.slice Z) (iso : fst ≫ f ≅ snd ≫ g),
      (CategoryTheory.Bicategory.PseudoPullbackCone.mk f g P fst snd iso).IsBilimit → Closed snd :=
  Iff.rfl

namespace forallScheme

/-- A universal scheme-valued 2-fibre-product condition witnesses
`forallScheme f`. -/
theorem of (h : ∀ {Z : Over S} {P : GroupoidsOver S} [AlgebraicStack P]
    {g : GroupoidsOver.slice Z ⟶ Y} {fst : P ⟶ X}
    {snd : P ⟶ GroupoidsOver.slice Z} (iso : fst ≫ f ≅ snd ≫ g),
    (CategoryTheory.Bicategory.PseudoPullbackCone.mk f g P fst snd iso).IsBilimit → Closed snd) : forallScheme f :=
  h

/-- Under `forallScheme f`, the test-leg of any scheme-valued 2-fibre product of
`f` is closed. -/
theorem spec (h : forallScheme f) {Z : Over S} {P : GroupoidsOver S}
    [AlgebraicStack P] {g : GroupoidsOver.slice Z ⟶ Y} {fst : P ⟶ X}
    {snd : P ⟶ GroupoidsOver.slice Z} (iso : fst ≫ f ≅ snd ≫ g)
    (hc : (CategoryTheory.Bicategory.PseudoPullbackCone.mk f g P fst snd iso).IsBilimit) : Closed snd :=
  h iso hc

end forallScheme

/-- `forallScheme f` is equivalent to closedness of every chosen scheme-valued
projection `Z ×_Y X ⟶ Z`. -/
theorem forallScheme_iff_twoFibreProduct_snd : forallScheme f ↔
    ∀ {Z : Over S} (g : GroupoidsOver.slice Z ⟶ Y),
      Closed (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- The projection of every affine-scheme-valued base change of `f` is a closed
map on points. -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {P : GroupoidsOver S} [AlgebraicStack P]
    {g : GroupoidsOver.slice Z ⟶ Y} {fst : P ⟶ X}
    {snd : P ⟶ GroupoidsOver.slice Z} (iso : fst ≫ f ≅ snd ≫ g),
    (CategoryTheory.Bicategory.PseudoPullbackCone.mk f g P fst snd iso).IsBilimit → Closed snd

/-- `forallAffine f` means every affine-scheme-valued 2-fibre-product projection
of `f` is a closed morphism. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (P : GroupoidsOver S) [AlgebraicStack P]
      (g : GroupoidsOver.slice Z ⟶ Y) (fst : P ⟶ X)
      (snd : P ⟶ GroupoidsOver.slice Z) (iso : fst ≫ f ≅ snd ≫ g),
      (CategoryTheory.Bicategory.PseudoPullbackCone.mk f g P fst snd iso).IsBilimit → Closed snd :=
  Iff.rfl

namespace forallAffine

/-- A universal affine-scheme-valued 2-fibre-product condition witnesses
`forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : GroupoidsOver S}
    [AlgebraicStack P] {g : GroupoidsOver.slice Z ⟶ Y} {fst : P ⟶ X}
    {snd : P ⟶ GroupoidsOver.slice Z} (iso : fst ≫ f ≅ snd ≫ g),
    (CategoryTheory.Bicategory.PseudoPullbackCone.mk f g P fst snd iso).IsBilimit → Closed snd) : forallAffine f :=
  h

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued 2-fibre
product of `f` is closed. -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {P : GroupoidsOver S} [AlgebraicStack P] {g : GroupoidsOver.slice Z ⟶ Y}
    {fst : P ⟶ X} {snd : P ⟶ GroupoidsOver.slice Z}
    (iso : fst ≫ f ≅ snd ≫ g) (hc : (CategoryTheory.Bicategory.PseudoPullbackCone.mk f g P fst snd iso).IsBilimit) :
    Closed snd :=
  h iso hc

end forallAffine

/-- `forallAffine f` is equivalent to closedness of every chosen affine
scheme-valued projection `Z ×_Y X ⟶ Z`. -/
theorem forallAffine_iff_twoFibreProduct_snd : forallAffine f ↔
    ∀ {Z : Over S} [IsAffine Z.left] (g : GroupoidsOver.slice Z ⟶ Y),
      Closed (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end Closed

namespace UniversallyClosed

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)

/-- There is a surjective smooth morphism from an algebraic space to `Y` along
which every 2-fibre-product base change of `f` is universally closed. -/
def existsSmoothOnTarget : Prop :=
  ∃ (V : AlgebraicSpace S) (p : V.toGroupoids ⟶ Y),
    Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
      ∀ {P : GroupoidsOver S} [AlgebraicStack P] {fst : P ⟶ X}
        {snd : P ⟶ V.toGroupoids} (iso : fst ≫ f ≅ snd ≫ p),
        (CategoryTheory.Bicategory.PseudoPullbackCone.mk f p P fst snd iso).IsBilimit → UniversallyClosed snd

/-- `existsSmoothOnTarget f` is the existence of a surjective smooth
algebraic-space atlas of `Y` along which 2-fibre-product base changes of `f`
are universally closed. -/
theorem existsSmoothOnTarget_iff : existsSmoothOnTarget f ↔
    ∃ (V : AlgebraicSpace S) (p : V.toGroupoids ⟶ Y),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
        ∀ (P : GroupoidsOver S) [AlgebraicStack P] (fst : P ⟶ X)
          (snd : P ⟶ V.toGroupoids) (iso : fst ≫ f ≅ snd ≫ p),
          (CategoryTheory.Bicategory.PseudoPullbackCone.mk f p P fst snd iso).IsBilimit → UniversallyClosed snd :=
  Iff.rfl

namespace existsSmoothOnTarget

/-- A surjective smooth algebraic-space atlas of `Y` with universally closed
2-fibre-product base changes of `f` witnesses `existsSmoothOnTarget f`. -/
theorem of {V : AlgebraicSpace S} (p : V.toGroupoids ⟶ Y)
    (hp_smooth : Groupoids.Hom.Smooth p) (hp_surj : Groupoids.Hom.Surjective p)
    (h : ∀ {P : GroupoidsOver S} [AlgebraicStack P] {fst : P ⟶ X}
      {snd : P ⟶ V.toGroupoids} (iso : fst ≫ f ≅ snd ≫ p),
      (CategoryTheory.Bicategory.PseudoPullbackCone.mk f p P fst snd iso).IsBilimit → UniversallyClosed snd) :
    existsSmoothOnTarget f :=
  ⟨V, p, hp_smooth, hp_surj, h⟩

/-- `existsSmoothOnTarget f` supplies a surjective smooth algebraic-space atlas
of `Y` along which 2-fibre-product base changes of `f` are universally closed. -/
theorem spec (h : existsSmoothOnTarget f) :
    ∃ (V : AlgebraicSpace S) (p : V.toGroupoids ⟶ Y),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
        ∀ {P : GroupoidsOver S} [AlgebraicStack P] {fst : P ⟶ X}
          {snd : P ⟶ V.toGroupoids} (iso : fst ≫ f ≅ snd ≫ p),
          (CategoryTheory.Bicategory.PseudoPullbackCone.mk f p P fst snd iso).IsBilimit → UniversallyClosed snd :=
  h

end existsSmoothOnTarget

/-- For a morphism `f : X ⟶ Y` of algebraic stacks, the following
are equivalent: `UniversallyClosed f`; for every scheme `Z` and morphism
`Z ⟶ Y` the projection `|Z ×_Y X| ⟶ |Z|` is closed; the same with `Z` affine;
and there exists an algebraic space `V` and a surjective smooth morphism
`V ⟶ Y` such that `V ×_Y X ⟶ V` is universally closed. -/
@[stacks 0CL3]
theorem tfae :
    List.TFAE [UniversallyClosed f, Closed.forallScheme f, Closed.forallAffine f,
      existsSmoothOnTarget f] :=
  sorry

/-- A morphism of algebraic stacks is universally closed iff every
scheme-valued base change has closed projection on points. -/
theorem iff_forallScheme : UniversallyClosed f ↔ Closed.forallScheme f :=
  (tfae f).out 0 1

/-- A morphism of algebraic stacks is universally closed iff every
affine-scheme-valued base change has closed projection on points. -/
theorem iff_forallAffine : UniversallyClosed f ↔ Closed.forallAffine f :=
  (tfae f).out 0 2

/-- A morphism of algebraic stacks is universally closed iff some surjective
smooth algebraic-space atlas of the target has universally closed base change. -/
theorem iff_existsSmoothOnTarget :
    UniversallyClosed f ↔ existsSmoothOnTarget f :=
  (tfae f).out 0 3

end UniversallyClosed

end AlgebraicGeometry.AlgebraicStack
