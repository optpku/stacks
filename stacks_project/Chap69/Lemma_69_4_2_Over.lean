/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_19_1_GeometricPoint

/-!
# Same-field geometric lifts along a morphism of algebraic spaces

A geometric point of `X` over a geometric point `ybar` of `Y`, with the same source
field `ybar.K`, is a morphism `Spec k ⟶ X` over `S` factoring `ybar`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

/-- A geometric point of `X` over `ybar` with the same source field `ybar.K`. -/
structure Over.{u} {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (ybar : GeometricPoint Y) where
  /-- The morphism `Spec k ⟶ X` from the spectrum of the field of `ybar`. -/
  hom : ofOver ybar.overObj ⟶ X
  /-- The morphism lies over `ybar`. -/
  fac : hom ≫ f = ybar.hom

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ybar : GeometricPoint Y)

/-- Construct a point of `X` over `ybar` from a factorization of `ybar.hom`. -/
def Over.of (hom : ofOver ybar.overObj ⟶ X) (fac : hom ≫ f = ybar.hom) :
    Over f ybar :=
  ⟨hom, fac⟩

variable {f ybar}

/-- The geometric point of `X` associated to a point of `X` over `ybar`. -/
def Over.toGeometricPoint (x : Over f ybar) : GeometricPoint X where
  K := ybar.K
  field := ybar.field
  structureHom := ybar.structureHom
  hom := x.hom
  isAlgClosed := ybar.isAlgClosed

/-- The morphism of `toGeometricPoint` is the stored morphism to `X`. -/
theorem Over.toGeometricPoint_hom (x : Over f ybar) :
    x.toGeometricPoint.hom = x.hom :=
  sorry

/-- Two points of `X` over `ybar` with the same morphism to `X` are equal. -/
theorem Over.ext {x₁ x₂ : Over f ybar} (h : x₁.hom = x₂.hom) :
    x₁ = x₂ :=
  sorry

/-- The geometric point associated to a lift of `ybar` maps to `ybar` under `f`. -/
theorem Over.toGeometricPoint_map (x : Over f ybar) :
    x.toGeometricPoint.map f = ybar :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
