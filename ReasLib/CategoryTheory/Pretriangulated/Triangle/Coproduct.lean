/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Coproducts of Triangles

This leaf constructs the objectwise coproduct of a family of triangles.  The
construction is independent of distinguishedness; the latter is a separate
proposition-level theorem under the pretriangulated hypotheses.
-/

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory.Pretriangulated

variable {I : Type w} {D : Type u} [Category.{v} D] [HasShift D ℤ]

/-- Stacks 0CRG: the objectwise coproduct triangle of a family `T`.

Its three objects are the chosen coproducts of the corresponding objects of
`T`; its third morphism lands in the shift of the coproduct of the first
objects, so no choice of a coproduct of shifted objects is part of the data. -/
@[stacks 0CRG]
def coproductTriangle (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] : Triangle D :=
  Triangle.mk
    (Sigma.desc (fun i ↦ (T i).mor₁ ≫ Sigma.ι (fun j ↦ (T j).obj₂) i))
    (Sigma.desc (fun i ↦ (T i).mor₂ ≫ Sigma.ι (fun j ↦ (T j).obj₃) i))
    (Sigma.desc (fun i ↦ (T i).mor₃ ≫ (Sigma.ι (fun j ↦ (T j).obj₁) i)⟦(1 : ℤ)⟧'))

/-- The first morphism of the objectwise coproduct triangle is the coproduct
descent of the first morphisms. -/
@[simp]
theorem coproductTriangle.mor₁ (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] :
    (coproductTriangle T).mor₁ =
      Sigma.desc (fun i ↦ (T i).mor₁ ≫ Sigma.ι (fun j ↦ (T j).obj₂) i) := sorry

/-- The second morphism of the objectwise coproduct triangle is the coproduct
descent of the second morphisms. -/
@[simp]
theorem coproductTriangle.mor₂ (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] :
    (coproductTriangle T).mor₂ =
      Sigma.desc (fun i ↦ (T i).mor₂ ≫ Sigma.ι (fun j ↦ (T j).obj₃) i) := sorry

/-- The third morphism of the objectwise coproduct triangle is the coproduct
descent of the shifted third morphisms. -/
@[simp]
theorem coproductTriangle.mor₃ (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] :
    (coproductTriangle T).mor₃ =
      Sigma.desc
        (fun i ↦ (T i).mor₃ ≫ (Sigma.ι (fun j ↦ (T j).obj₁) i)⟦(1 : ℤ)⟧') := sorry

/-- The first compatibility square for the canonical inclusion of a triangle
into its objectwise coproduct. -/
@[reassoc]
theorem coproductTriangle.ι_comm₁ (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] (i : I) :
    (T i).mor₁ ≫ Sigma.ι (fun j ↦ (T j).obj₂) i =
      Sigma.ι (fun j ↦ (T j).obj₁) i ≫ (coproductTriangle T).mor₁ := sorry

/-- The second compatibility square for the canonical inclusion of a triangle
into its objectwise coproduct. -/
@[reassoc]
theorem coproductTriangle.ι_comm₂ (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] (i : I) :
    (T i).mor₂ ≫ Sigma.ι (fun j ↦ (T j).obj₃) i =
      Sigma.ι (fun j ↦ (T j).obj₂) i ≫ (coproductTriangle T).mor₂ := sorry

/-- The third compatibility square for the canonical inclusion of a triangle
into its objectwise coproduct. -/
@[reassoc]
theorem coproductTriangle.ι_comm₃ (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] (i : I) :
    (T i).mor₃ ≫ (Sigma.ι (fun j ↦ (T j).obj₁) i)⟦(1 : ℤ)⟧' =
      Sigma.ι (fun j ↦ (T j).obj₃) i ≫ (coproductTriangle T).mor₃ := sorry

/-- The canonical inclusion of the `i`th triangle into the objectwise
coproduct triangle. -/
@[stacks 0CRG]
def coproductTriangle.ι (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] (i : I) :
    T i ⟶ coproductTriangle T :=
  Triangle.homMk _ _
    (Sigma.ι (fun j ↦ (T j).obj₁) i)
    (Sigma.ι (fun j ↦ (T j).obj₂) i)
    (Sigma.ι (fun j ↦ (T j).obj₃) i)
    (coproductTriangle.ι_comm₁ T i)
    (coproductTriangle.ι_comm₂ T i)
    (coproductTriangle.ι_comm₃ T i)

/-- The first component of `coproductTriangle.ι`. -/
@[simp]
theorem coproductTriangle.ι_hom₁ (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] (i : I) :
    (coproductTriangle.ι T i).hom₁ = Sigma.ι (fun j ↦ (T j).obj₁) i := sorry

/-- The second component of `coproductTriangle.ι`. -/
@[simp]
theorem coproductTriangle.ι_hom₂ (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] (i : I) :
    (coproductTriangle.ι T i).hom₂ = Sigma.ι (fun j ↦ (T j).obj₂) i := sorry

/-- The third component of `coproductTriangle.ι`. -/
@[simp]
theorem coproductTriangle.ι_hom₃ (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] (i : I) :
    (coproductTriangle.ι T i).hom₃ = Sigma.ι (fun j ↦ (T j).obj₃) i := sorry

/-- The first compatibility square for the coproduct descent of a family of
triangle morphisms. -/
@[reassoc]
theorem coproductTriangle.desc_comm₁ (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] {S : Triangle D} (φ : ∀ i, T i ⟶ S) :
    (coproductTriangle T).mor₁ ≫ Sigma.desc (fun i ↦ (φ i).hom₂) =
      Sigma.desc (fun i ↦ (φ i).hom₁) ≫ S.mor₁ := sorry

/-- The second compatibility square for the coproduct descent of a family of
triangle morphisms. -/
@[reassoc]
theorem coproductTriangle.desc_comm₂ (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] {S : Triangle D} (φ : ∀ i, T i ⟶ S) :
    (coproductTriangle T).mor₂ ≫ Sigma.desc (fun i ↦ (φ i).hom₃) =
      Sigma.desc (fun i ↦ (φ i).hom₂) ≫ S.mor₂ := sorry

/-- The third compatibility square for the coproduct descent of a family of
triangle morphisms. -/
@[reassoc]
theorem coproductTriangle.desc_comm₃ (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] {S : Triangle D} (φ : ∀ i, T i ⟶ S) :
    (coproductTriangle T).mor₃ ≫ (Sigma.desc (fun i ↦ (φ i).hom₁))⟦(1 : ℤ)⟧' =
      Sigma.desc (fun i ↦ (φ i).hom₃) ≫ S.mor₃ := sorry

/-- The coproduct descent of a family of triangle morphisms with common target. -/
@[stacks 0CRG]
def coproductTriangle.desc (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] {S : Triangle D} (φ : ∀ i, T i ⟶ S) :
    coproductTriangle T ⟶ S :=
  Triangle.homMk _ _
    (Sigma.desc (fun i ↦ (φ i).hom₁))
    (Sigma.desc (fun i ↦ (φ i).hom₂))
    (Sigma.desc (fun i ↦ (φ i).hom₃))
    (coproductTriangle.desc_comm₁ T φ)
    (coproductTriangle.desc_comm₂ T φ)
    (coproductTriangle.desc_comm₃ T φ)

/-- The first component of `coproductTriangle.desc`. -/
@[simp]
theorem coproductTriangle.desc_hom₁ (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] {S : Triangle D} (φ : ∀ i, T i ⟶ S) :
    (coproductTriangle.desc T φ).hom₁ = Sigma.desc (fun i ↦ (φ i).hom₁) := sorry

/-- The second component of `coproductTriangle.desc`. -/
@[simp]
theorem coproductTriangle.desc_hom₂ (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] {S : Triangle D} (φ : ∀ i, T i ⟶ S) :
    (coproductTriangle.desc T φ).hom₂ = Sigma.desc (fun i ↦ (φ i).hom₂) := sorry

/-- The third component of `coproductTriangle.desc`. -/
@[simp]
theorem coproductTriangle.desc_hom₃ (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] {S : Triangle D} (φ : ∀ i, T i ⟶ S) :
    (coproductTriangle.desc T φ).hom₃ = Sigma.desc (fun i ↦ (φ i).hom₃) := sorry

/-- A coproduct inclusion followed by the corresponding triangle-level descent
recovers the supplied triangle morphism. -/
@[reassoc]
theorem coproductTriangle.ι_desc (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] {S : Triangle D} (φ : ∀ i, T i ⟶ S) (i : I) :
    coproductTriangle.ι T i ≫ coproductTriangle.desc T φ = φ i := sorry

/-- Morphisms out of an objectwise coproduct triangle are determined by their
composites with all canonical inclusions. -/
@[ext]
theorem coproductTriangle.hom_ext (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] {S : Triangle D}
    (f g : coproductTriangle T ⟶ S)
    (h : ∀ i, coproductTriangle.ι T i ≫ f = coproductTriangle.ι T i ≫ g) : f = g := sorry

/-- The cofan of triangles whose point is `coproductTriangle T`. -/
@[stacks 0CRG]
def coproductTriangle.cofan (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] : Cofan T :=
  Cofan.mk (coproductTriangle T) (coproductTriangle.ι T)

/-- The factorization formula for `coproductTriangle.cofan`. -/
@[reassoc]
theorem coproductTriangle.cofan_fac (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] (S : Cofan T) (i : I) :
    (coproductTriangle.cofan T).inj i ≫ coproductTriangle.desc T S.inj = S.inj i := sorry

/-- The uniqueness formula for `coproductTriangle.cofan`. -/
theorem coproductTriangle.cofan_uniq (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] (S : Cofan T) (f : coproductTriangle T ⟶ S.pt)
    (h : ∀ i, (coproductTriangle.cofan T).inj i ≫ f = S.inj i) :
    f = coproductTriangle.desc T S.inj := sorry

/-- The objectwise coproduct triangle is the coproduct of the family `T` in
the category of triangles. -/
@[stacks 0CRG]
def coproductTriangle.isColimitCofan (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] : IsColimit (coproductTriangle.cofan T) :=
  Cofan.IsColimit.mk (coproductTriangle.cofan T)
    (fun S ↦ coproductTriangle.desc T S.inj)
    (fun S i ↦ coproductTriangle.cofan_fac T S i)
    (fun S f h ↦ coproductTriangle.cofan_uniq T S f h)

/-- Three objectwise coproducts supply a coproduct in the category of triangles. -/
instance coproductTriangle.hasCoproduct (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] : HasCoproduct T :=
  HasColimit.mk ⟨coproductTriangle.cofan T, coproductTriangle.isColimitCofan T⟩

/-- The standard coproduct of triangles is canonically isomorphic to the
objectwise construction, for any choice of the standard coproduct. -/
def coproductTriangle.iso (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] [HasCoproduct T] :
    ∐ T ≅ coproductTriangle T :=
  colimit.isoColimitCocone
    ⟨coproductTriangle.cofan T, coproductTriangle.isColimitCofan T⟩

/-- The comparison identifies the standard and objectwise coproduct inclusions. -/
@[reassoc (attr := simp)]
theorem coproductTriangle.ι_iso_hom (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] [HasCoproduct T] (i : I) :
    Sigma.ι T i ≫ (coproductTriangle.iso T).hom = coproductTriangle.ι T i := by
  exact colimit.isoColimitCocone_ι_hom
    ⟨coproductTriangle.cofan T, coproductTriangle.isColimitCofan T⟩ (Discrete.mk i)

/-- The inverse comparison identifies the objectwise and standard inclusions. -/
@[reassoc (attr := simp)]
theorem coproductTriangle.ι_iso_inv (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] [HasCoproduct T] (i : I) :
    coproductTriangle.ι T i ≫ (coproductTriangle.iso T).inv = Sigma.ι T i := by
  exact colimit.isoColimitCocone_ι_inv
    ⟨coproductTriangle.cofan T, coproductTriangle.isColimitCofan T⟩ (Discrete.mk i)

section Distinguished

variable [HasZeroObject D] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]

/-- Stacks 0CRG: the objectwise coproduct of distinguished triangles is
distinguished whenever the three objectwise coproducts exist. -/
@[stacks 0CRG]
theorem coproductTriangle_distinguished (T : I → Triangle D)
    (hT : ∀ i, T i ∈ distTriang D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] :
    coproductTriangle T ∈ distTriang D := sorry

end Distinguished

end CategoryTheory.Pretriangulated
