/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RepresentableConditions

/-!
# Relative ampleness on algebraic spaces and schemes

Relative ampleness on an algebraic space with scheme target can be tested after
identifying both spaces with schemes.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Scheme-relative ampleness of `L` after identifying `X` and `Y` with schemes
over `S` via `eX` and `eY`. -/
def RelativelyAmple.schemeRelativelyAmple {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {U V : Over S} (eX : X ≅ ofOver U) (eY : Y ≅ ofOver V) (f : X ⟶ Y)
    (L : X.Modules) : Prop :=
  AlgebraicGeometry.RelativelyAmple
    (Yoneda.fullyFaithful.preimage (eX.inv ≫ f ≫ eY.hom : yoneda.obj U ⟶ yoneda.obj V)).left
    ((Modules.restrictToScheme U).obj ((Modules.pullback eX.inv).obj L))

/-- `schemeRelativelyAmple` unfolds to relative ampleness of the restricted
pullback along the induced morphism of schemes. -/
theorem RelativelyAmple.schemeRelativelyAmple_iff {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {U V : Over S} (eX : X ≅ ofOver U)
    (eY : Y ≅ ofOver V) (f : X ⟶ Y) (L : X.Modules) :
    RelativelyAmple.schemeRelativelyAmple eX eY f L ↔
      AlgebraicGeometry.RelativelyAmple
        (Yoneda.fullyFaithful.preimage
          (eX.inv ≫ f ≫ eY.hom : yoneda.obj U ⟶ yoneda.obj V)).left
        ((Modules.restrictToScheme U).obj ((Modules.pullback eX.inv).obj L)) :=
  by
    rfl

/-- For an invertible module and scheme target, relative ampleness on an
algebraic space is equivalent to scheme-relative ampleness after all scheme
presentations of source and target. -/
theorem RelativelyAmple.iff_schemeRelativelyAmple {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (L : X.Modules)
    [MonoidalCategory.isInvertibleObject L] [IsScheme Y] :
    RelativelyAmple f L ↔
      IsScheme X ∧
        ∀ {U V : Over S} (eX : X ≅ ofOver U) (eY : Y ≅ ofOver V),
          RelativelyAmple.schemeRelativelyAmple eX eY f L :=
  sorry

/-- Relative ampleness over a scheme implies that the source is a scheme. -/
theorem RelativelyAmple.isScheme {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (L : X.Modules) [IsScheme Y] [RelativelyAmple f L] :
    IsScheme X :=
  IsScheme.of_relativelyRepresentable f (RelativelyAmple.representable L)

/-- For a morphism of schemes viewed as algebraic spaces, relative ampleness is
equivalent to relative ampleness of the restricted module on schemes. -/
theorem RelativelyAmple.iff_restrictToScheme {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) (L : (ofOver U).Modules) :
    RelativelyAmple (AlgebraicSpace.ofOverMap h) L ↔
      AlgebraicGeometry.RelativelyAmple h.left ((Modules.restrictToScheme U).obj L) :=
  sorry

/-- Relative ampleness of a morphism of schemes viewed as algebraic spaces
gives relative ampleness of the restricted module. -/
instance RelativelyAmple.restrictToScheme {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) (L : (ofOver U).Modules)
    [RelativelyAmple (AlgebraicSpace.ofOverMap h) L] :
    AlgebraicGeometry.RelativelyAmple h.left ((Modules.restrictToScheme U).obj L) :=
  (RelativelyAmple.iff_restrictToScheme h L).mp inferInstance

end AlgebraicGeometry.AlgebraicSpace
