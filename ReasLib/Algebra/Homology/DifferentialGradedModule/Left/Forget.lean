/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Forget
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Left

/-!
# Underlying complexes of left differential graded modules

This file exposes the underlying cochain complex of a left differential graded module directly
from its graded family and differential.  In particular, forgetting the action does not pass
through the opposite-module equivalence and imposes no universe equality between the algebra and
module carriers.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace LeftDifferentialGradedModule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R}

/-- Consecutive underlying differentials of a left differential graded module compose to zero. -/
theorem d_comp_d (M : LeftDifferentialGradedModule.{u, v} A) (n : ℤ) :
    ModuleCat.ofHom (M.d n) ≫ ModuleCat.ofHom (M.d (n + 1)) = 0 := sorry

/-- The underlying cochain complex of a left differential graded module. -/
@[stacks 0FQD "underlying complex of a left differential graded module"]
def toCochainComplex (M : LeftDifferentialGradedModule.{u, v} A) :
    CochainComplex (ModuleCat.{v} R) ℤ :=
  CochainComplex.of M.X (fun n ↦ ModuleCat.ofHom (M.d n)) (d_comp_d M)

/-- The degree-`n` object of the underlying complex is the degree-`n` module. -/
@[simp]
theorem toCochainComplex_X (M : LeftDifferentialGradedModule.{u, v} A) (n : ℤ) :
    M.toCochainComplex.X n = M.X n := sorry

/-- The underlying-complex differential is the differential of the left DG module. -/
@[simp]
theorem toCochainComplex_d (M : LeftDifferentialGradedModule.{u, v} A) (n : ℤ) :
    M.toCochainComplex.d n (n + 1) = ModuleCat.ofHom (M.d n) := sorry

namespace Hom

/-- The cochain map underlying a morphism of left differential graded modules. -/
def toCochainMap {M N : LeftDifferentialGradedModule.{u, v} A} (f : M ⟶ N) :
    M.toCochainComplex ⟶ N.toCochainComplex :=
  { f := fun n ↦ ModuleCat.ofHom (f.hom n)
    comm' := sorry }

/-- The degree-`n` component of an underlying left-module cochain map. -/
@[simp]
theorem toCochainMap_f {M N : LeftDifferentialGradedModule.{u, v} A}
    (f : M ⟶ N) (n : ℤ) :
    f.toCochainMap.f n = ModuleCat.ofHom (f.hom n) := sorry

/-- A left-DG-module morphism is determined by its underlying cochain map. -/
theorem toCochainMap_injective {M N : LeftDifferentialGradedModule.{u, v} A} :
    Function.Injective (fun f : M ⟶ N ↦ f.toCochainMap) := sorry

end Hom

/-- Forget a left action while retaining the underlying cochain complex. -/
@[stacks 0FQD "forgetful functor for left differential graded modules"]
def forgetToComplex (A : CochainDGAlgebra.{u, w} R) :
    LeftDifferentialGradedModule.{u, v} A ⥤ CochainComplex (ModuleCat.{v} R) ℤ where
  obj M := M.toCochainComplex
  map f := Hom.toCochainMap f
  map_id := sorry
  map_comp := sorry

/-- Forgetting a left DG module returns its underlying cochain complex. -/
@[simp]
theorem forgetToComplex_obj (A : CochainDGAlgebra.{u, w} R)
    (M : LeftDifferentialGradedModule.{u, v} A) :
    (forgetToComplex A).obj M = M.toCochainComplex := sorry

/-- Forgetting a left-module morphism returns its underlying cochain map. -/
@[simp]
theorem forgetToComplex_map (A : CochainDGAlgebra.{u, w} R)
    {M N : LeftDifferentialGradedModule.{u, v} A} (f : M ⟶ N) :
    (forgetToComplex A).map f = f.toCochainMap := sorry

/-- The left-module forgetful functor is faithful. -/
instance forgetToComplexFaithful (A : CochainDGAlgebra.{u, w} R) :
    Functor.Faithful (forgetToComplex A) := sorry

/-- The underlying complex of a left DG module has homology in every degree. -/
instance instHasHomology (M : LeftDifferentialGradedModule.{u, v} A) (n : ℤ) :
    M.toCochainComplex.HasHomology n := sorry

/-- The cycles of a left differential graded module in degree `n`. -/
abbrev cycles (M : LeftDifferentialGradedModule.{u, v} A) (n : ℤ) :=
  M.toCochainComplex.cycles n

/-- The homology of a left differential graded module in degree `n`. -/
abbrev homology (M : LeftDifferentialGradedModule.{u, v} A) (n : ℤ) :=
  M.toCochainComplex.homology n

/-- Degree-`n` cycles of left DG modules, obtained from their underlying complexes. -/
@[stacks 0FQD "degreewise cycles functor for left differential graded modules"]
def cyclesFunctor (A : CochainDGAlgebra.{u, w} R) (n : ℤ) :
    LeftDifferentialGradedModule.{u, v} A ⥤ ModuleCat.{v} R :=
  forgetToComplex A ⋙
    HomologicalComplex.cyclesFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) n

/-- Evaluating the left-module cycles functor gives underlying-complex cycles. -/
@[simp]
theorem cyclesFunctor_obj (A : CochainDGAlgebra.{u, w} R)
    (M : LeftDifferentialGradedModule.{u, v} A) (n : ℤ) :
    (cyclesFunctor A n).obj M = M.cycles n := sorry

/-- The map on left-module cycles is induced by the underlying cochain map. -/
@[simp]
theorem cyclesFunctor_map (A : CochainDGAlgebra.{u, w} R)
    {M N : LeftDifferentialGradedModule.{u, v} A} (f : M ⟶ N) (n : ℤ) :
    (cyclesFunctor A n).map f =
      HomologicalComplex.cyclesMap (Hom.toCochainMap f) n := sorry

/-- Degree-`n` homology of left DG modules, obtained from their underlying complexes. -/
@[stacks 0FQD "degreewise homology functor for left differential graded modules"]
def homologyFunctor (A : CochainDGAlgebra.{u, w} R) (n : ℤ) :
    LeftDifferentialGradedModule.{u, v} A ⥤ ModuleCat.{v} R :=
  forgetToComplex A ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) n

/-- Evaluating the left-module homology functor gives underlying-complex homology. -/
@[simp]
theorem homologyFunctor_obj (A : CochainDGAlgebra.{u, w} R)
    (M : LeftDifferentialGradedModule.{u, v} A) (n : ℤ) :
    (homologyFunctor A n).obj M = M.homology n := sorry

/-- The map on left-module homology is induced by the underlying cochain map. -/
@[simp]
theorem homologyFunctor_map (A : CochainDGAlgebra.{u, w} R)
    {M N : LeftDifferentialGradedModule.{u, v} A} (f : M ⟶ N) (n : ℤ) :
    (homologyFunctor A n).map f =
      HomologicalComplex.homologyMap (Hom.toCochainMap f) n := sorry

end LeftDifferentialGradedModule
