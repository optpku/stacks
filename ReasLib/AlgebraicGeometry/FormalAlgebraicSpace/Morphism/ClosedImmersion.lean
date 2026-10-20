module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Pullback
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Basic

/-!
# Closed immersions of presheaves over a scheme

A morphism of presheaves over a scheme is a closed immersion when it is
representable by algebraic spaces and every scheme Yoneda pullback is a closed
immersion of algebraic spaces. This property is stable under arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- A morphism of functors of points on schemes over `S` is a closed
immersion when it is representable by algebraic spaces and every Yoneda
pullback is a closed immersion of algebraic spaces. -/
@[mk_iff]
class ClosedImmersion {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    Prop where
  /-- `f` is representable by algebraic spaces. -/
  representable : representableByAlgebraicSpaces f
  /-- Every Yoneda pullback of `f` is a closed immersion of algebraic spaces. -/
  of_pullback :
    ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
      AlgebraicSpace.IsClosedImmersion (representableByAlgebraicSpaces.pullbackHom representable ξ)

namespace ClosedImmersion

/-- A morphism of functors of points is a closed immersion if and only if it is
representable by algebraic spaces and every Yoneda pullback is a closed
immersion of algebraic spaces. -/
theorem iff {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    ClosedImmersion f ↔
      ∃ (h : representableByAlgebraicSpaces f),
        ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
          AlgebraicSpace.IsClosedImmersion (representableByAlgebraicSpaces.pullbackHom h ξ) :=
  sorry

/-- The identity morphism of a functor of points is a closed immersion. -/
instance id {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} : ClosedImmersion (𝟙 X) :=
  sorry

/-- The composite of two closed immersions of presheaves over a scheme is a closed
immersion of formal algebraic spaces. -/
@[stacks 0GHW]
instance comp {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    [ClosedImmersion f] [ClosedImmersion g] :
    ClosedImmersion (f ≫ g) :=
  sorry

/-- A closed immersion is representable by algebraic spaces. -/
theorem relativelyRepresentable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) [ClosedImmersion f] : representableByAlgebraicSpaces f :=
  sorry

/-- Yoneda pullbacks of a closed immersion are closed immersions of algebraic
spaces. -/
theorem spec {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    [hf : ClosedImmersion f] {U : Over S} (ξ : yoneda.obj U ⟶ Y) :
    representableByAlgebraicSpaces f ∧
      AlgebraicSpace.IsClosedImmersion (representableByAlgebraicSpaces.pullbackHom hf.representable ξ) :=
  sorry

end ClosedImmersion

/-- In a pullback square of presheaves over a scheme, the base change of a
closed immersion is a closed immersion. -/
theorem closedImmersion_of_isPullback {S : Scheme.{u}}
    {X Y Y' B : (Over S)ᵒᵖ ⥤ Type u}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : ClosedImmersion g) :
    ClosedImmersion g' :=
  sorry

/-- The base-change projection `pullback.snd f g` of a closed immersion
`f : X ⟶ Y` of presheaves over a scheme is a closed immersion. -/
instance closedImmersion_pullback_snd {S : Scheme.{u}}
    {X Y Z : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Z ⟶ Y)
    [HasPullback f g] [ClosedImmersion f] : ClosedImmersion (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
