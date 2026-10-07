module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap66.«66_27_0_4_Comparison»
public import stacks_project.Chap71.Lemma_71_14_3_RelativelyAmple

/-!
# Relative ampleness: algebraic spaces versus schemes

When the target of a morphism of algebraic spaces is a scheme, relative
ampleness in the algebraic-space sense is equivalent to the source being a
scheme and relative ampleness in the scheme sense.
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
    (ofOverPreimage (eX.inv ≫ f ≫ eY.hom)).left
    ((Modules.restrictToScheme U).obj ((Modules.pullback eX.inv).obj L))

/-- `schemeRelativelyAmple` is scheme-relative ampleness of the restricted
pullback of `L` along the underlying morphism of schemes over `S`. -/
theorem RelativelyAmple.schemeRelativelyAmple_iff {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {U V : Over S} (eX : X ≅ ofOver U)
    (eY : Y ≅ ofOver V) (f : X ⟶ Y) (L : X.Modules) :
    RelativelyAmple.schemeRelativelyAmple eX eY f L ↔
      AlgebraicGeometry.RelativelyAmple
        (ofOverPreimage (eX.inv ≫ f ≫ eY.hom)).left
        ((Modules.restrictToScheme U).obj ((Modules.pullback eX.inv).obj L)) :=
  sorry

/-- Lemma 71.14.2: let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Let `L` be an invertible `𝒪_X`-module. Assume `Y` is a scheme.
Then `L` is ample on `X/Y` in the sense of Definition 71.14.1 if and only if `X`
is a scheme and `L` is ample on `X/Y` in the sense of Morphisms, Definition
29.37.1. -/
@[stacks 0D32]
theorem RelativelyAmple.iff_schemeRelativelyAmple {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (L : X.Modules) [IsScheme Y] :
    RelativelyAmple f L ↔
      IsScheme X ∧
        ∀ {U V : Over S} (eX : X ≅ ofOver U) (eY : Y ≅ ofOver V),
          RelativelyAmple.schemeRelativelyAmple eX eY f L :=
  sorry

/-- Relative ampleness over a scheme implies that the source is a scheme. -/
theorem RelativelyAmple.isScheme {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (L : X.Modules) [IsScheme Y] [RelativelyAmple f L] :
    IsScheme X :=
  sorry

/-- On schemes-as-spaces, algebraic-space relative ampleness of `ofOverMap h` is
equivalent to scheme-relative ampleness of `h.left`. -/
theorem RelativelyAmple.iff_restrictToScheme {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) (L : (ofOver U).Modules) :
    RelativelyAmple (AlgebraicSpace.ofOverMap h) L ↔
      AlgebraicGeometry.RelativelyAmple h.left ((Modules.restrictToScheme U).obj L) :=
  sorry

/-- Algebraic-space relative ampleness of `ofOverMap h` implies scheme-relative
ampleness of the underlying morphism of schemes. -/
instance RelativelyAmple.restrictToScheme {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) (L : (ofOver U).Modules)
    [RelativelyAmple (AlgebraicSpace.ofOverMap h) L] :
    AlgebraicGeometry.RelativelyAmple h.left ((Modules.restrictToScheme U).obj L) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
