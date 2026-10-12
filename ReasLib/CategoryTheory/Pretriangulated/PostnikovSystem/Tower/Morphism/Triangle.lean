/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Morphism.Basic
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Triangle

/-!
# Stage-Triangle Morphisms of Sequential Postnikov Towers

This leaf exposes the triangle morphism induced at each stage of a tower
morphism, together with its component and functoriality API.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Tower.Hom

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable {T T' T'' : Tower D}

/-- The canonical morphism between the stage triangles induced by a tower morphism. -/
@[stacks 0D8Z]
def triangleMorphism (f : Hom T T') (n : ℕ) :
    T.triangle n ⟶ T'.triangle n :=
  Triangle.homMk _ _ (f.yMap (n + 1)) (f.xMap (n + 1)) (f.yMap n)
    (f.comm_toX n.succ).w (f.comm_toNext n).w (f.comm_connecting n).w

/-- The first component of the stage triangle morphism is the next auxiliary map. -/
@[simp, stacks 0D8Z]
theorem triangleMorphism.hom₁ (f : Hom T T') (n : ℕ) :
    (triangleMorphism f n).hom₁ = f.yMap (n + 1) := sorry

/-- The second component of the stage triangle morphism is the next row-object map. -/
@[simp, stacks 0D8Z]
theorem triangleMorphism.hom₂ (f : Hom T T') (n : ℕ) :
    (triangleMorphism f n).hom₂ = f.xMap (n + 1) := sorry

/-- The third component of the stage triangle morphism is the current auxiliary map. -/
@[simp, stacks 0D8Z]
theorem triangleMorphism.hom₃ (f : Hom T T') (n : ℕ) :
    (triangleMorphism f n).hom₃ = f.yMap n := sorry

/-- The stage triangle morphism induced by an identity tower morphism is an identity. -/
@[simp, stacks 0D8Z]
theorem triangleMorphism.id (T : Tower D) (n : ℕ) :
    triangleMorphism (id T) n = 𝟙 (T.triangle n) := sorry

/-- The stage triangle morphism induced by a composite is the composite of the induced maps. -/
@[simp, stacks 0D8Z]
theorem triangleMorphism.comp (f : Hom T T') (g : Hom T' T'') (n : ℕ) :
    triangleMorphism (comp f g) n =
      triangleMorphism f n ≫ triangleMorphism g n := sorry

end CategoryTheory.PostnikovSystem.Tower.Hom
