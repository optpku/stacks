/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.GradedModule.Preadditive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Shifts of graded modules over a differential graded algebra

This leaf constructs the grading shift in the tensor-morphism model of graded modules.  The
shift is independent of a differential: degree `n` after shifting by `k` is degree `n + k`
before shifting.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedAlgebra.GradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf J CommRingCat.{w}}

namespace Shift

/-- Reassociation of the module-action target after a grading shift. -/
theorem actionIndex (n m k : ℤ) : (n + k) + m = (n + m) + k := by abel

/-- Shift a graded right module by `k`, so that its degree-`n` object is the original
degree-`n + k` object. -/
@[stacks 0FQ1 "grading shift of a graded module over a sheaf of differential graded algebras"]
def obj {A : DGA(O)} (M : GradedModule A) (k : ℤ) : GradedModule A where
  obj n := M.obj (n + k)
  smul n m :=
    M.smul (n + k) m ≫ eqToHom (congrArg M.obj (actionIndex n m k))
  smul_assoc := by
    intro n m l
    simp only [comp_whiskerRight, eqToHom_whiskerRight, Category.assoc]
    rw [← eqToHom_naturality_assoc
      (f := fun t ↦ M.obj t ⊗ A.toComplex.X l) (g := fun t ↦ M.obj (t + l))
      (fun t ↦ M.smul t l) (actionIndex n m k)]
    simpa only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc] using
      congrArg (fun f ↦ f ≫ eqToHom (congrArg M.obj (actionIndex n (m + l) k)))
        (M.smul_assoc (n + k) m l)
  one_smul := by
    intro n
    simpa [Category.assoc] using M.one_smul (n + k)

/-- Evaluation of a shifted graded module is evaluation in the translated degree. -/
@[simp]
theorem obj_apply {A : DGA(O)} (M : GradedModule A) (k n : ℤ) :
    (obj M k).obj n = M.obj (n + k) := rfl

/-- The action on a shifted graded module is the original action followed by degree transport. -/
@[simp]
theorem obj_smul {A : DGA(O)} (M : GradedModule A) (k n m : ℤ) :
    (obj M k).smul n m =
      M.smul (n + k) m ≫ eqToHom (congrArg M.obj (actionIndex n m k)) := rfl

/-- Shift a morphism of graded modules degreewise. -/
def map {A : DGA(O)} {M N : GradedModule A} (f : M ⟶ N) (k : ℤ) :
    obj M k ⟶ obj N k where
  hom n := f.hom (n + k)
  comm := by
    intro n m
    change
      (M.smul (n + k) m ≫
          eqToHom (congrArg M.obj (actionIndex n m k))) ≫ f.hom ((n + m) + k) =
        (f.hom (n + k) ▷ A.toComplex.X m) ≫
          (N.smul (n + k) m ≫
            eqToHom (congrArg N.obj (actionIndex n m k)))
    calc
      (M.smul (n + k) m ≫
          eqToHom (congrArg M.obj (actionIndex n m k))) ≫ f.hom ((n + m) + k) =
          M.smul (n + k) m ≫
            (f.hom ((n + k) + m) ≫
              eqToHom (congrArg N.obj (actionIndex n m k))) := by
        rw [Category.assoc]
        congr 1
        simpa using (eqToHom_naturality (f := M.obj) (g := N.obj)
          (fun t ↦ f.hom t) (actionIndex n m k)).symm
      _ = (f.hom (n + k) ▷ A.toComplex.X m) ≫
          N.smul (n + k) m ≫
            eqToHom (congrArg N.obj (actionIndex n m k)) := by
        rw [← Category.assoc]
        exact congrArg (fun q ↦ q ≫ eqToHom (congrArg N.obj (actionIndex n m k)))
          (f.comm (n + k) m)

/-- A shifted graded-module morphism is evaluated in the translated degree. -/
@[simp]
theorem map_hom {A : DGA(O)} {M N : GradedModule A} (f : M ⟶ N) (k n : ℤ) :
    (map f k).hom n = f.hom (n + k) := rfl

/-- Shifting by a fixed integer is an endofunctor on graded modules. -/
def functor (A : DGA(O)) (k : ℤ) : GradedModule A ⥤ GradedModule A where
  obj M := obj M k
  map f := map f k
  map_id := by
    intros M
    apply Hom.ext
    funext n
    rfl
  map_comp := by
    intros M N P f g
    apply Hom.ext
    funext n
    rfl

/-- The grading-shift functor acts on objects by the explicit shift. -/
@[simp]
theorem functor_obj (A : DGA(O)) (M : GradedModule A) (k : ℤ) :
    (functor A k).obj M = obj M k := rfl

/-- The grading-shift functor acts on morphisms degreewise. -/
@[simp]
theorem functor_map (A : DGA(O)) {M N : GradedModule A} (f : M ⟶ N) (k : ℤ) :
    (functor A k).map f = map f k := rfl

/-- Every grading-shift functor is additive. -/
instance functor_additive (A : DGA(O)) (k : ℤ) : (functor A k).Additive where
  map_add := by
    intros M N f g
    apply Hom.ext
    funext n
    rfl

end Shift

/-- Scoped notation for the grading shift of a graded module over a differential graded
algebra. -/
scoped[DifferentialGradedAlgebra.GradedModule] notation:max M:max "[" k:max "]" =>
  _root_.SheafOfModules.RingedSite.DifferentialGradedAlgebra.GradedModule.Shift.obj M k

end SheafOfModules.RingedSite.DifferentialGradedAlgebra.GradedModule

end
