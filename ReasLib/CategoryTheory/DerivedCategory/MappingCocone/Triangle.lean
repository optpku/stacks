/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Comparison triangles for mapping cocones

The canonical mapping-cocone triangle is often presented after replacing its first term by a
quasi-isomorphic complex.  This leaf owns that replacement generically in an abelian category;
site-specific Mayer--Vietoris files only instantiate it with section complexes.
-/

open CategoryTheory CategoryTheory.Pretriangulated
open CochainComplex

universe w v u

namespace CategoryTheory.DerivedCategory.MappingCocone

variable {C : Type u} [Category.{v} C]

section

variable [Preadditive C]

/-- The zero degree-`(-1)` cochain satisfies the relation defining the canonical lift of a
two-step complex into the mapping cocone. -/
@[stacks 0F16 "zero-cochain mapping-cocone lift"]
theorem zeroLiftCondition
    {IX IZY IE : CochainComplex C ℤ}
    (α : IX ⟶ IZY) (β : IZY ⟶ IE) (hαβ : α ≫ β = 0) :
    CochainComplex.HomComplex.δ (-1) 0
          (0 : CochainComplex.HomComplex.Cochain IX IE (-1)) +
        CochainComplex.HomComplex.Cochain.ofHom (α ≫ β) =
      0 := sorry

end

section

variable [Abelian C] [HasDerivedCategory.{w} C]

/-- The derived triangle obtained by replacing the first term of the mapping-cocone triangle by a
complex whose image is isomorphic to the mapping cocone. -/
noncomputable def triangleOfComparison
    {IX IZY IE : CochainComplex C ℤ} (β : IZY ⟶ IE) (c : IX ⟶ mappingCocone β)
    [IsIso (DerivedCategory.Q.map c)] :
    Triangle (DerivedCategory C) :=
  Triangle.mk
    (DerivedCategory.Q.map (c ≫ mappingCocone.fst β))
    (DerivedCategory.Q.map β)
    ((DerivedCategory.Q.mapTriangle.obj (mappingCocone.triangle β)).mor₃ ≫
      (asIso (DerivedCategory.Q.map c)).inv⟦(1 : ℤ)⟧')

/-- The first square commutes for the comparison of a mapping-cocone triangle. -/
theorem triangleOfComparison_comm₁
    {IX IZY IE : CochainComplex C ℤ} (β : IZY ⟶ IE) (c : IX ⟶ mappingCocone β)
    [IsIso (DerivedCategory.Q.map c)] :
    (triangleOfComparison β c).mor₁ ≫ (Iso.refl _).hom =
      (asIso (DerivedCategory.Q.map c)).hom ≫
        (DerivedCategory.Q.mapTriangle.obj (mappingCocone.triangle β)).mor₁ := sorry

/-- The second square commutes for the comparison of a mapping-cocone triangle. -/
theorem triangleOfComparison_comm₂
    {IX IZY IE : CochainComplex C ℤ} (β : IZY ⟶ IE) (c : IX ⟶ mappingCocone β)
    [IsIso (DerivedCategory.Q.map c)] :
    (triangleOfComparison β c).mor₂ ≫ (Iso.refl _).hom =
      (Iso.refl _).hom ≫
        (DerivedCategory.Q.mapTriangle.obj (mappingCocone.triangle β)).mor₂ := sorry

/-- The shifted third square commutes for the comparison of a mapping-cocone triangle. -/
theorem triangleOfComparison_comm₃
    {IX IZY IE : CochainComplex C ℤ} (β : IZY ⟶ IE) (c : IX ⟶ mappingCocone β)
    [IsIso (DerivedCategory.Q.map c)] :
    (triangleOfComparison β c).mor₃ ≫
        (asIso (DerivedCategory.Q.map c)).hom⟦(1 : ℤ)⟧' =
      (Iso.refl _).hom ≫
        (DerivedCategory.Q.mapTriangle.obj (mappingCocone.triangle β)).mor₃ := sorry

/-- The replacement triangle is canonically isomorphic to the mapping-cocone triangle. -/
noncomputable def triangleOfComparisonIso
    {IX IZY IE : CochainComplex C ℤ} (β : IZY ⟶ IE) (c : IX ⟶ mappingCocone β)
    [IsIso (DerivedCategory.Q.map c)] :
    triangleOfComparison β c ≅
      DerivedCategory.Q.mapTriangle.obj (mappingCocone.triangle β) :=
  let e : DerivedCategory.Q.obj IX ≅
      DerivedCategory.Q.obj (CochainComplex.mappingCocone β) :=
    asIso (DerivedCategory.Q.map c)
  Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _)
    (triangleOfComparison_comm₁ β c)
    (triangleOfComparison_comm₂ β c)
    (triangleOfComparison_comm₃ β c)

/-- The comparison triangle is distinguished whenever the first comparison becomes an isomorphism
in the derived category. -/
@[stacks 0F16 "distinguished comparison triangle"]
theorem triangleOfComparison_distinguished
    {IX IZY IE : CochainComplex C ℤ} (β : IZY ⟶ IE) (c : IX ⟶ mappingCocone β)
    [IsIso (DerivedCategory.Q.map c)] :
    triangleOfComparison β c ∈ distTriang (DerivedCategory C) := sorry

/-- Two comparison complexes mapping isomorphically to the same mapping cocone are canonically
isomorphic in the derived category. -/
noncomputable def comparisonIso
    {IX₁ IX₂ IZY IE : CochainComplex C ℤ} (β : IZY ⟶ IE)
    (c₁ : IX₁ ⟶ mappingCocone β) (c₂ : IX₂ ⟶ mappingCocone β)
    [IsIso (DerivedCategory.Q.map c₁)] [IsIso (DerivedCategory.Q.map c₂)] :
    DerivedCategory.Q.obj IX₁ ≅ DerivedCategory.Q.obj IX₂ :=
  (asIso (DerivedCategory.Q.map c₁)) ≪≫ (asIso (DerivedCategory.Q.map c₂)).symm

/-- The canonical comparison between two choices intertwines their maps to the fixed cocone. -/
@[simp, reassoc]
theorem comparisonIso_hom_comp
    {IX₁ IX₂ IZY IE : CochainComplex C ℤ} (β : IZY ⟶ IE)
    (c₁ : IX₁ ⟶ mappingCocone β) (c₂ : IX₂ ⟶ mappingCocone β)
    [IsIso (DerivedCategory.Q.map c₁)] [IsIso (DerivedCategory.Q.map c₂)] :
    (comparisonIso β c₁ c₂).hom ≫ DerivedCategory.Q.map c₂ =
      DerivedCategory.Q.map c₁ := sorry

end

end CategoryTheory.DerivedCategory.MappingCocone

end
