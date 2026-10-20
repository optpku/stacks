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
theorem actionIndex (n m k : ℤ) : (n + k) + m = (n + m) + k := sorry

/-- Shift a graded right module by `k`, so that its degree-`n` object is the original
degree-`n + k` object. -/
@[stacks 0FQ1 "grading shift of a graded module over a sheaf of differential graded algebras"]
def obj {A : DGA(O)} (M : GradedModule A) (k : ℤ) : GradedModule A where
  obj n := M.obj (n + k)
  smul n m :=
    M.smul (n + k) m ≫ eqToHom (congrArg M.obj (actionIndex n m k))
  smul_assoc := sorry
  one_smul := sorry

/-- Evaluation of a shifted graded module is evaluation in the translated degree. -/
@[simp]
theorem obj_apply {A : DGA(O)} (M : GradedModule A) (k n : ℤ) :
    (obj M k).obj n = M.obj (n + k) := sorry

/-- The action on a shifted graded module is the original action followed by degree transport. -/
@[simp]
theorem obj_smul {A : DGA(O)} (M : GradedModule A) (k n m : ℤ) :
    (obj M k).smul n m =
      M.smul (n + k) m ≫ eqToHom (congrArg M.obj (actionIndex n m k)) := sorry

/-- Shift a morphism of graded modules degreewise. -/
def map {A : DGA(O)} {M N : GradedModule A} (f : M ⟶ N) (k : ℤ) :
    obj M k ⟶ obj N k where
  hom n := f.hom (n + k)
  comm := sorry

/-- A shifted graded-module morphism is evaluated in the translated degree. -/
@[simp]
theorem map_hom {A : DGA(O)} {M N : GradedModule A} (f : M ⟶ N) (k n : ℤ) :
    (map f k).hom n = f.hom (n + k) := sorry

/-- Shifting by a fixed integer is an endofunctor on graded modules. -/
def functor (A : DGA(O)) (k : ℤ) : GradedModule A ⥤ GradedModule A where
  obj M := obj M k
  map f := map f k
  map_id := sorry
  map_comp := sorry

/-- The grading-shift functor acts on objects by the explicit shift. -/
@[simp]
theorem functor_obj (A : DGA(O)) (M : GradedModule A) (k : ℤ) :
    (functor A k).obj M = obj M k := sorry

/-- The grading-shift functor acts on morphisms degreewise. -/
@[simp]
theorem functor_map (A : DGA(O)) {M N : GradedModule A} (f : M ⟶ N) (k : ℤ) :
    (functor A k).map f = map f k := sorry

/-- Every grading-shift functor is additive. -/
instance functor_additive (A : DGA(O)) (k : ℤ) : (functor A k).Additive := sorry

end Shift

/-- Scoped notation for the grading shift of a graded module over a differential graded
algebra. -/
scoped[DifferentialGradedAlgebra.GradedModule] notation:max M:max "[" k:max "]" =>
  _root_.SheafOfModules.RingedSite.DifferentialGradedAlgebra.GradedModule.Shift.obj M k

end SheafOfModules.RingedSite.DifferentialGradedAlgebra.GradedModule

end
