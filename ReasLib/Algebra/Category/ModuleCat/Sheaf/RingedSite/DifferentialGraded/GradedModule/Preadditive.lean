/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.GradedModule

/-!
# Preadditive graded module categories

The additive structure is transported from degreewise maps in the ambient module category.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

section


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {𝒪 : Sheaf J CommRingCat.{w}}

namespace DifferentialGradedAlgebra.GradedModule

/-- The zero graded-module morphism is computed degreewise. -/
instance instZeroHom {𝒜 : DGA(𝒪)} (M N : GradedModule 𝒜) : Zero (Hom M N) where
  zero :=
    { hom := fun _ ↦ 0
      comm := sorry }

/-- Addition of graded-module morphisms is computed degreewise. -/
instance instAddHom {𝒜 : DGA(𝒪)} (M N : GradedModule 𝒜) : Add (Hom M N) where
  add f g :=
    { hom := fun n ↦ f.hom n + g.hom n
      comm := sorry }

/-- Negation of graded-module morphisms is computed degreewise. -/
instance instNegHom {𝒜 : DGA(𝒪)} (M N : GradedModule 𝒜) : Neg (Hom M N) where
  neg f :=
    { hom := fun n ↦ -f.hom n
      comm := sorry }

/-- Subtraction of graded-module morphisms is computed degreewise. -/
instance instSubHom {𝒜 : DGA(𝒪)} (M N : GradedModule 𝒜) : Sub (Hom M N) where
  sub f g :=
    { hom := fun n ↦ f.hom n - g.hom n
      comm := sorry }

/-- Natural-number scalar multiplication of graded-module morphisms is computed degreewise. -/
instance instSMulNatHom {𝒜 : DGA(𝒪)} (M N : GradedModule 𝒜) : SMul ℕ (Hom M N) where
  smul k f :=
    { hom := fun n ↦ k • f.hom n
      comm := sorry }

/-- Integer scalar multiplication of graded-module morphisms is computed degreewise. -/
instance instSMulIntHom {𝒜 : DGA(𝒪)} (M N : GradedModule 𝒜) : SMul ℤ (Hom M N) where
  smul k f :=
    { hom := fun n ↦ k • f.hom n
      comm := sorry }

/-- A sum of graded-module morphisms is computed degreewise. -/
@[simp]
theorem add_hom {𝒜 : DGA(𝒪)} {M N : GradedModule 𝒜} (f g : Hom M N) (n : ℤ) :
    (f + g).hom n = f.hom n + g.hom n := sorry

/-- The zero graded-module morphism is computed degreewise. -/
@[simp]
theorem zero_hom {𝒜 : DGA(𝒪)} (M N : GradedModule 𝒜) (n : ℤ) :
    (0 : Hom M N).hom n = 0 := sorry

/-- Negation of a graded-module morphism is computed degreewise. -/
@[simp]
theorem neg_hom {𝒜 : DGA(𝒪)} {M N : GradedModule 𝒜} (f : Hom M N) (n : ℤ) :
    (-f).hom n = -f.hom n := sorry

/-- Subtraction of graded-module morphisms is computed degreewise. -/
@[simp]
theorem sub_hom {𝒜 : DGA(𝒪)} {M N : GradedModule 𝒜}
    (f g : Hom M N) (n : ℤ) :
    (f - g).hom n = f.hom n - g.hom n := sorry

/-- Natural scalar multiplication of graded-module morphisms is computed degreewise. -/
@[simp]
theorem nsmul_hom {𝒜 : DGA(𝒪)} {M N : GradedModule 𝒜}
    (k : ℕ) (f : Hom M N) (n : ℤ) :
    (k • f).hom n = k • f.hom n := sorry

/-- Integer scalar multiplication of graded-module morphisms is computed degreewise. -/
@[simp]
theorem zsmul_hom {𝒜 : DGA(𝒪)} {M N : GradedModule 𝒜}
    (k : ℤ) (f : Hom M N) (n : ℤ) :
    (k • f).hom n = k • f.hom n := sorry

/-- Graded-module morphisms form an additive commutative group. -/
instance instAddCommGroupHom {𝒜 : DGA(𝒪)} (M N : GradedModule 𝒜) :
    AddCommGroup (Hom M N) :=
  Function.Injective.addCommGroup
    (fun f : Hom M N ↦ f.hom)
    hom_injective
    sorry
    (fun _ _ ↦ sorry)
    (fun _ ↦ sorry)
    (fun _ _ ↦ sorry)
    (fun _ _ ↦ sorry)
    (fun _ _ ↦ sorry)

/-- Graded modules over a fixed differential graded algebra form a preadditive category. -/
instance instPreadditive (𝒜 : DGA(𝒪)) : Preadditive (GradedModule 𝒜) where
  homGroup M N := instAddCommGroupHom M N
  add_comp := sorry
  comp_add := sorry

end DifferentialGradedAlgebra.GradedModule

end


end SheafOfModules.RingedSite
