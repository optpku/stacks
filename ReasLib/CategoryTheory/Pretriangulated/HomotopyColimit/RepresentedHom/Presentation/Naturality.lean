/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.RepresentedHom.Functor
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.RepresentedHom.Presentation.ShortComplex
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of presentation precomposition

Target postcomposition commutes with contravariant presentation precomposition. The resulting
short-complex maps form a natural transformation between represented Hom functors.
@stack 0CQX
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

universe u v

namespace CategoryTheory.HomotopyColimit.RepresentedHom

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- Target postcomposition commutes with contravariant presentation precomposition. -/
@[reassoc, stacks 0CQX]
theorem shortComplexPrecomp_naturality
    {K L : ℕ ⥤ D} {α : K ⟶ L} {X Y Z W : D}
    {P : Presentation K X} {Q : Presentation L Y}
    (φ : Presentation.Hom α P Q) (f : Z ⟶ W) :
    shortComplexMap Q f ≫ shortComplexPrecomp φ W =
      shortComplexPrecomp φ Z ≫ shortComplexMap P f := sorry

/-- Presentation precomposition is natural with respect to the represented Hom
short-complex functors. -/
@[reassoc, stacks 0CQX]
theorem presentationPrecomp_naturality
    {K L : ℕ ⥤ D} {α : K ⟶ L} {X Y Z W : D}
    {P : Presentation K X} {Q : Presentation L Y}
    (φ : Presentation.Hom α P Q) (f : Z ⟶ W) :
    (functor Q).map f ≫ shortComplexPrecomp φ W =
      shortComplexPrecomp φ Z ≫ (functor P).map f := sorry

/-- A presentation morphism gives a natural transformation between the represented Hom
short-complex functors in the contravariant direction. -/
@[stacks 0CQX]
def presentationNatTrans {K L : ℕ ⥤ D} {α : K ⟶ L} {X Y : D}
    {P : Presentation K X} {Q : Presentation L Y}
    (φ : Presentation.Hom α P Q) : functor Q ⟶ functor P where
  app Z := shortComplexPrecomp φ Z
  naturality := fun {Z W} f ↦
    presentationPrecomp_naturality (Z := Z) (W := W) φ f

/-- The component of `presentationNatTrans` is the corresponding short-complex
precomposition map. -/
@[simp]
theorem presentationNatTrans_app {K L : ℕ ⥤ D} {α : K ⟶ L} {X Y : D}
    {P : Presentation K X} {Q : Presentation L Y}
    (φ : Presentation.Hom α P Q) (Z : D) :
    (presentationNatTrans φ).app Z = shortComplexPrecomp φ Z := sorry

end CategoryTheory.HomotopyColimit.RepresentedHom

end
