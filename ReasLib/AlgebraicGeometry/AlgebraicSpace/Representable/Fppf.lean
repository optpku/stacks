/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Property
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation

/-!
# Representable surjective fppf morphisms

Representable morphisms of functors of points are surjective, flat, and locally
of finite presentation when their scheme Yoneda pullbacks have these properties.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}

/-- A morphism of functors of points is representable by algebraic spaces,
surjective, flat, and locally of finite presentation when every scheme Yoneda
pullback has these three properties. -/
def representableSurjectiveFppf (g : X ⟶ Y) : Prop :=
  AlgebraicSpace.relativeAlgebraicSpaces
    (fun _ _ h ↦ AlgebraicSpace.Surjective h ∧ AlgebraicSpace.Flat h ∧
      AlgebraicSpace.LocallyOfFinitePresentation h) g

/-- `representableSurjectiveFppf g` means `g` is representable by algebraic spaces
and every scheme Yoneda pullback is surjective, flat, and locally of finite
presentation. -/
theorem representableSurjectiveFppf_iff (g : X ⟶ Y) :
    representableSurjectiveFppf g ↔
      AlgebraicSpace.representableByAlgebraicSpaces g ∧
        ∀ (hg : AlgebraicSpace.representableByAlgebraicSpaces g) ⦃U : Over S⦄
          (ξ : yoneda.obj U ⟶ Y),
          AlgebraicSpace.Surjective (hg.pullbackHom ξ) ∧
            AlgebraicSpace.Flat (hg.pullbackHom ξ) ∧
              AlgebraicSpace.LocallyOfFinitePresentation (hg.pullbackHom ξ) :=
  Iff.rfl

namespace representableSurjectiveFppf

/-- A morphism representable by algebraic spaces whose scheme Yoneda pullbacks
are surjective, flat, and locally of finite presentation witnesses
`representableSurjectiveFppf`. -/
theorem of {g : X ⟶ Y} (hg : AlgebraicSpace.representableByAlgebraicSpaces g)
    (h : ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
      AlgebraicSpace.Surjective (hg.pullbackHom ξ) ∧
        AlgebraicSpace.Flat (hg.pullbackHom ξ) ∧
          AlgebraicSpace.LocallyOfFinitePresentation (hg.pullbackHom ξ)) :
    representableSurjectiveFppf g :=
  ⟨hg, fun _ ↦ h⟩

/-- `representableSurjectiveFppf g` supplies representability by algebraic spaces
together with surjectivity, flatness, and local finite presentation of every scheme
Yoneda pullback. -/
theorem spec {g : X ⟶ Y} (h : representableSurjectiveFppf g) :
    AlgebraicSpace.representableByAlgebraicSpaces g ∧
      ∀ (hg : AlgebraicSpace.representableByAlgebraicSpaces g) ⦃U : Over S⦄
        (ξ : yoneda.obj U ⟶ Y),
        AlgebraicSpace.Surjective (hg.pullbackHom ξ) ∧
          AlgebraicSpace.Flat (hg.pullbackHom ξ) ∧
            AlgebraicSpace.LocallyOfFinitePresentation (hg.pullbackHom ξ) :=
  h

end representableSurjectiveFppf

end AlgebraicGeometry.AlgebraicSpace
