/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Endpoint-Normalized Degreewise-Split Triangle Models

Mathlib characterizes distinguished triangles in a homotopy category up to an
arbitrary triangle isomorphism. This leaf records the stronger normal form in
which the first and third complexes are fixed and the comparison is the
identity on those two vertices.
-/

noncomputable section

open CategoryTheory.Limits CategoryTheory.Pretriangulated ComplexShape

universe v u

namespace CategoryTheory.HomotopyCategory

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasZeroObject A]
  [HasBinaryBiproducts A]

/-- An endpoint-normalized degreewise-split model of a triangle in the
homotopy category of cochain complexes. -/
@[stacks 0G6C]
structure DegreewiseSplitModel {X Y Z : CochainComplex A ℤ}
    (f : (HomotopyCategory.quotient A (up ℤ)).obj X ⟶
      (HomotopyCategory.quotient A (up ℤ)).obj Y)
    (g : (HomotopyCategory.quotient A (up ℤ)).obj Y ⟶
      (HomotopyCategory.quotient A (up ℤ)).obj Z)
    (h : (HomotopyCategory.quotient A (up ℤ)).obj Z ⟶
      ((HomotopyCategory.quotient A (up ℤ)).obj X)⟦(1 : ℤ)⟧) where
  /-- The middle complex of the normalized model. -/
  middle : CochainComplex A ℤ
  /-- The inclusion into the middle complex. -/
  ι : X ⟶ middle
  /-- The projection from the middle complex. -/
  π : middle ⟶ Z
  /-- The two maps form a short complex. -/
  zero : ι ≫ π = 0
  /-- The short complex is split in every degree. -/
  splitting : ∀ n : ℤ,
    ((ShortComplex.mk ι π zero).map
      (HomologicalComplex.eval A (up ℤ) n)).Splitting
  /-- The original triangle is isomorphic to the degreewise-split model. -/
  iso : Triangle.mk f g h ≅
    CochainComplex.trianglehOfDegreewiseSplit
      (ShortComplex.mk ι π zero) splitting
  /-- The comparison is the identity on the first vertex. -/
  iso_hom₁ : iso.hom.hom₁ = 𝟙 ((HomotopyCategory.quotient A (up ℤ)).obj X)
  /-- The comparison is the identity on the third vertex. -/
  iso_hom₃ : iso.hom.hom₃ = 𝟙 ((HomotopyCategory.quotient A (up ℤ)).obj Z)

namespace DegreewiseSplitModel

variable {X Y Z : CochainComplex A ℤ}
  {f : (HomotopyCategory.quotient A (up ℤ)).obj X ⟶
    (HomotopyCategory.quotient A (up ℤ)).obj Y}
  {g : (HomotopyCategory.quotient A (up ℤ)).obj Y ⟶
    (HomotopyCategory.quotient A (up ℤ)).obj Z}
  {h : (HomotopyCategory.quotient A (up ℤ)).obj Z ⟶
    ((HomotopyCategory.quotient A (up ℤ)).obj X)⟦(1 : ℤ)⟧}

/-- The degreewise-split short complex underlying a normalized model. -/
abbrev shortComplex (M : DegreewiseSplitModel f g h) :
    ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk M.ι M.π M.zero

/-- The degreewise-split triangle underlying a normalized model. -/
noncomputable abbrev triangle (M : DegreewiseSplitModel f g h) :
    Triangle (HomotopyCategory A (up ℤ)) :=
  CochainComplex.trianglehOfDegreewiseSplit M.shortComplex M.splitting

/-- The first morphism of the model triangle is induced by its inclusion. -/
@[simp]
theorem triangle_mor₁ (M : DegreewiseSplitModel f g h) :
    M.triangle.mor₁ = (HomotopyCategory.quotient A (up ℤ)).map M.ι := sorry

/-- The second morphism of the model triangle is induced by its projection. -/
@[simp]
theorem triangle_mor₂ (M : DegreewiseSplitModel f g h) :
    M.triangle.mor₂ = (HomotopyCategory.quotient A (up ℤ)).map M.π := sorry

/-- The degreewise-split triangle underlying a normalized model is
distinguished. -/
theorem triangle_distinguished (M : DegreewiseSplitModel f g h) :
    M.triangle ∈ distTriang (HomotopyCategory A (up ℤ)) := sorry

/-- The source triangle of a normalized model is distinguished. -/
theorem source_distinguished (M : DegreewiseSplitModel f g h) :
    Triangle.mk f g h ∈ distTriang (HomotopyCategory A (up ℤ)) := sorry

/-- Endpoint normalization makes the connecting morphism of the model
literally equal to that of the source triangle. -/
@[simp]
theorem triangle_mor₃ (M : DegreewiseSplitModel f g h) :
    M.triangle.mor₃ = h := sorry

end DegreewiseSplitModel

namespace DegreewiseSplitModel

/-- Stacks 0G6C: every distinguished triangle in the homotopy category of
cochain complexes has an endpoint-normalized degreewise-split model. -/
@[stacks 0G6C]
theorem nonempty_of_distinguished {X Y Z : CochainComplex A ℤ}
    {f : (HomotopyCategory.quotient A (up ℤ)).obj X ⟶
      (HomotopyCategory.quotient A (up ℤ)).obj Y}
    {g : (HomotopyCategory.quotient A (up ℤ)).obj Y ⟶
      (HomotopyCategory.quotient A (up ℤ)).obj Z}
    {h : (HomotopyCategory.quotient A (up ℤ)).obj Z ⟶
      ((HomotopyCategory.quotient A (up ℤ)).obj X)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang (HomotopyCategory A (up ℤ))) :
    Nonempty (DegreewiseSplitModel f g h) := sorry

/-- A triangle is distinguished exactly when it has an endpoint-normalized
degreewise-split model. -/
theorem distinguished_iff_nonempty
    {X Y Z : CochainComplex A ℤ}
    {f : (HomotopyCategory.quotient A (up ℤ)).obj X ⟶
      (HomotopyCategory.quotient A (up ℤ)).obj Y}
    {g : (HomotopyCategory.quotient A (up ℤ)).obj Y ⟶
      (HomotopyCategory.quotient A (up ℤ)).obj Z}
    {h : (HomotopyCategory.quotient A (up ℤ)).obj Z ⟶
      ((HomotopyCategory.quotient A (up ℤ)).obj X)⟦(1 : ℤ)⟧} :
    Triangle.mk f g h ∈ distTriang (HomotopyCategory A (up ℤ)) ↔
      Nonempty (DegreewiseSplitModel f g h) := sorry

end DegreewiseSplitModel

end CategoryTheory.HomotopyCategory
