/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Preadditive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Underlying Complexes of Differential Graded Modules

This leaf owns the underlying cochain complex of a right differential graded module, the
faithful linear forgetful functor to cochain complexes, and the induced homology functors.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra R}

/-- Consecutive underlying differentials of a right differential graded module compose to zero. -/
theorem d_comp_d (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    ModuleCat.ofHom (M.d n) ≫ ModuleCat.ofHom (M.d (n + 1)) = 0 := sorry

/-- The underlying cochain complex of a right differential graded module. -/
@[stacks 09K1 "underlying cochain complex of a differential graded module"]
noncomputable def toCochainComplex (M : DifferentialGradedModule.{u, v} A) :
    CochainComplex (ModuleCat.{v} R) ℤ :=
  CochainComplex.of M.X (fun n ↦ ModuleCat.ofHom (M.d n)) (d_comp_d M)

/-- A right differential graded module coerces to its underlying cochain complex. -/
instance instCoeOut :
    CoeOut (DifferentialGradedModule.{u, v} A) (CochainComplex (ModuleCat.{v} R) ℤ) where
  coe := toCochainComplex

/-- The degree-`n` object of the underlying cochain complex is the degree-`n` module. -/
@[simp]
theorem toCochainComplex_X (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    M.toCochainComplex.X n = M.X n := sorry

/-- The underlying complex differential is the differential of the differential graded module. -/
@[simp]
theorem toCochainComplex_d (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    M.toCochainComplex.d n (n + 1) = ModuleCat.ofHom (M.d n) := sorry

namespace Hom

/-- The cochain map underlying a morphism of right differential graded modules. -/
def toCochainMap {M N : DifferentialGradedModule.{u, v} A} (f : Hom M N) :
    M.toCochainComplex ⟶ N.toCochainComplex where
  f n := ModuleCat.ofHom (f.hom n)
  comm' := sorry

/-- The degree-`n` component of the underlying cochain map is the original linear map. -/
@[simp]
theorem toCochainMap_f {M N : DifferentialGradedModule.{u, v} A} (f : Hom M N) (n : ℤ) :
    f.toCochainMap.f n = ModuleCat.ofHom (f.hom n) := sorry

/-- A differential graded module morphism is determined by its underlying cochain map. -/
theorem toCochainMap_injective {M N : DifferentialGradedModule.{u, v} A} :
    Function.Injective (fun f : Hom M N ↦ f.toCochainMap) := sorry

end Hom

/-- Forget the right action while retaining the underlying cochain complex. -/
@[stacks 09K1 "forgetful functor from differential graded modules to complexes"]
def forgetToComplex (A : CochainDGAlgebra R) :
    DifferentialGradedModule.{u, v} A ⥤ CochainComplex (ModuleCat.{v} R) ℤ where
  obj M := M.toCochainComplex
  map f := Hom.toCochainMap f
  map_id := sorry
  map_comp := sorry

/-- Forgetting a right differential graded module returns its underlying cochain complex. -/
@[simp]
theorem forgetToComplex_obj (A : CochainDGAlgebra R)
    (M : DifferentialGradedModule.{u, v} A) :
    (forgetToComplex A).obj M = M.toCochainComplex := sorry

/-- Forgetting a morphism returns its underlying cochain map. -/
@[simp]
theorem forgetToComplex_map (A : CochainDGAlgebra R)
    {M N : DifferentialGradedModule.{u, v} A} (f : M ⟶ N) :
    (forgetToComplex A).map f = Hom.toCochainMap f := sorry

/-- The degree-`n` component of a forgotten morphism is its original linear component. -/
@[simp]
theorem forgetToComplex_map_f (A : CochainDGAlgebra R)
    {M N : DifferentialGradedModule.{u, v} A} (f : M ⟶ N) (n : ℤ) :
    ((forgetToComplex A).map f).f n = ModuleCat.ofHom (f.hom n) := sorry

/-- Forgetting to the underlying cochain complex is faithful. -/
instance forgetToComplex_faithful (A : CochainDGAlgebra R) :
    Functor.Faithful (forgetToComplex.{u, v} A) where
  map_injective := fun {_ _} _ _ h ↦ Hom.toCochainMap_injective h

/-- Forgetting to the underlying cochain complex preserves addition. -/
instance forgetToComplex_additive (A : CochainDGAlgebra R) :
    (forgetToComplex.{u, v} A).Additive where
  map_add := sorry

/-- Forgetting to the underlying cochain complex is `R`-linear. -/
instance forgetToComplex_linear (A : CochainDGAlgebra R) :
    Functor.Linear R (forgetToComplex.{u, v} A) where
  map_smul := sorry

/-- The underlying cochain complex has homology in every degree. -/
noncomputable instance instHasHomology (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    M.toCochainComplex.HasHomology n :=
  ⟨⟨ShortComplex.HomologyData.ofAbelian (M.toCochainComplex.sc n)⟩⟩

/-- The cycles object of a right differential graded module in degree `n`. -/
noncomputable abbrev cycles (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :=
  M.toCochainComplex.cycles n

/-- The canonical inclusion of cycles into the degree-`n` module. -/
noncomputable abbrev iCycles (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    M.cycles n ⟶ M.X n :=
  M.toCochainComplex.iCycles n

/-- The homology object of a right differential graded module in degree `n`. -/
noncomputable abbrev homology (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :=
  M.toCochainComplex.homology n

/-- The canonical projection from cycles to homology in degree `n`. -/
noncomputable abbrev homologyπ (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    M.cycles n ⟶ M.homology n :=
  M.toCochainComplex.homologyπ n

/-- Degree-`n` cycles of right differential graded modules, obtained from the underlying
cochain-complex cycles functor. -/
@[stacks 09K1 "degreewise cycles functor for differential graded modules"]
noncomputable def cyclesFunctor (A : CochainDGAlgebra R) (n : ℤ) :
    DifferentialGradedModule.{u, v} A ⥤ ModuleCat.{v} R :=
  forgetToComplex A ⋙
    HomologicalComplex.cyclesFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) n

/-- Evaluating the cycles functor gives the cycles of the underlying cochain complex. -/
@[simp]
theorem cyclesFunctor_obj (A : CochainDGAlgebra R)
    (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (cyclesFunctor A n).obj M = M.cycles n := sorry

/-- The cycles map of a differential graded module morphism is the cycles map of its
underlying cochain map. -/
@[simp]
theorem cyclesFunctor_map (A : CochainDGAlgebra R)
    {M N : DifferentialGradedModule.{u, v} A} (f : M ⟶ N) (n : ℤ) :
    (cyclesFunctor A n).map f =
      HomologicalComplex.cyclesMap (Hom.toCochainMap f) n := sorry

/-- Degree-`n` homology of right differential graded modules, obtained from the underlying
cochain-complex homology functor. -/
noncomputable def homologyFunctor (A : CochainDGAlgebra R) (n : ℤ) :
    DifferentialGradedModule.{u, v} A ⥤ ModuleCat.{v} R :=
  forgetToComplex A ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) n

/-- Evaluating the homology functor gives the homology of the underlying cochain complex. -/
@[simp]
theorem homologyFunctor_obj (A : CochainDGAlgebra R)
    (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (homologyFunctor A n).obj M = M.homology n := sorry

/-- The homology map of a differential graded module morphism is the homology map of its
underlying cochain map. -/
@[simp]
theorem homologyFunctor_map (A : CochainDGAlgebra R)
    {M N : DifferentialGradedModule.{u, v} A} (f : M ⟶ N) (n : ℤ) :
    (homologyFunctor A n).map f =
      HomologicalComplex.homologyMap (Hom.toCochainMap f) n := sorry

end DifferentialGradedModule
