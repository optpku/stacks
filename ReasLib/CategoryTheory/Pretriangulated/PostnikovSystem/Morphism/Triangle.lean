/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Morphism.Basic
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Stages.Triangle

@[expose] public section

/-!
# Stage Triangles of Postnikov-System Morphisms

This file exposes the triangle morphism induced at each stage of a morphism of
finite Postnikov systems, together with its component and functoriality API.
-/

open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.PostnikovSystem.Morphism

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable {n : ℕ} {X X' : ComposableArrows D n}
variable {P : PostnikovSystem X} {P' : PostnikovSystem X'} {φ : X ⟶ X'}

/-- The canonical morphism between the stage triangles induced by a Postnikov-system morphism. -/
@[stacks 0D7Z]
def triangleMorphism (ψ : PostnikovSystem.Morphism P P' φ) (i : Fin n) :
    P.triangle i ⟶ P'.triangle i :=
  Triangle.homMk _ _ (ψ.yMap i.castSucc) (φ.app i.castSucc) (ψ.yMap i.succ)
    (ψ.comm_toX i.castSucc).w (ψ.comm_toNext i).w (ψ.comm_connecting i).w

/-- The first component of the stage triangle morphism is the corresponding auxiliary-object
map. -/
@[stacks 0D7Z, simp]
theorem triangleMorphism.hom₁ (ψ : PostnikovSystem.Morphism P P' φ) (i : Fin n) :
    (triangleMorphism ψ i).hom₁ = ψ.yMap i.castSucc := sorry

/-- The second component of the stage triangle morphism is the corresponding row-map
component. -/
@[stacks 0D7Z, simp]
theorem triangleMorphism.hom₂ (ψ : PostnikovSystem.Morphism P P' φ) (i : Fin n) :
    (triangleMorphism ψ i).hom₂ = φ.app i.castSucc := sorry

/-- The third component of the stage triangle morphism is the next auxiliary-object map. -/
@[stacks 0D7Z, simp]
theorem triangleMorphism.hom₃ (ψ : PostnikovSystem.Morphism P P' φ) (i : Fin n) :
    (triangleMorphism ψ i).hom₃ = ψ.yMap i.succ := sorry

/-- Passing the identity Postnikov-system morphism to a stage gives the identity triangle
morphism. -/
@[stacks 0D7Z, simp]
theorem triangleMorphism.id (P : PostnikovSystem X) (i : Fin n) :
    triangleMorphism (PostnikovSystem.Morphism.id P) i = 𝟙 (P.triangle i) := sorry

/-- Passing a composite Postnikov-system morphism to a stage gives the composite of the stage
triangle morphisms. -/
@[stacks 0D7Z, simp]
theorem triangleMorphism.comp
    {X'' : ComposableArrows D n} {P'' : PostnikovSystem X''} {φ' : X' ⟶ X''}
    (ψ : PostnikovSystem.Morphism P P' φ) (χ : PostnikovSystem.Morphism P' P'' φ')
    (i : Fin n) :
    triangleMorphism (PostnikovSystem.Morphism.comp ψ χ) i =
      triangleMorphism ψ i ≫ triangleMorphism χ i := sorry

end CategoryTheory.PostnikovSystem.Morphism
