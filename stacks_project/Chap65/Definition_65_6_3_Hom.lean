/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism

/-!
# Morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is a morphism of their functors of points.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The component of a morphism of algebraic spaces at an object of `(Over S)ᵒᵖ`. -/
def hom_app {S : Scheme.{u}} {F F' : AlgebraicSpace S} (f : Hom F F')
    (T : (Over S)ᵒᵖ) : F.functorOfPoints.obj T ⟶ F'.functorOfPoints.obj T :=
  f.app T

/-- The component of `hom_app f` at `T` is the component of the underlying natural
transformation. -/
theorem hom_app_def {S : Scheme.{u}} {F F' : AlgebraicSpace S} (f : Hom F F')
    (T : (Over S)ᵒᵖ) : hom_app f T = f.app T :=
  rfl

/-- The identity morphism of an algebraic space is the identity transformation of its
functor of points. -/
theorem id_hom {S : Scheme.{u}} (F : AlgebraicSpace S) :
    𝟙 F = 𝟙 (F.functorOfPoints) :=
  rfl

/-- Composition of morphisms of algebraic spaces is composition of the corresponding
transformations of functors of points. -/
theorem comp_hom {S : Scheme.{u}} {F F' F'' : AlgebraicSpace S}
    (f : F ⟶ F') (g : F' ⟶ F'') :
    f ≫ g = NatTrans.vcomp f g :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
