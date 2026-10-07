module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap76.Lemma_76_52_4_Relative
public import stacks_project.Chap86.«86_3_2_1_Pushforward»

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- The structure sheaf of an algebraic space, placed in degree zero, has quasi-coherent
cohomology. -/
theorem singleFunctor_unit_mem {S : Scheme.{u}} (X : AlgebraicSpace S) :
    derivedQuasiCoherentModuleProperty X
      ((DerivedCategory.singleFunctor (Modules X) 0).obj
        (SheafOfModules.unit (structureSheaf X) : X.Modules)) :=
  sorry

/-- The structure sheaf `𝒪_X`, placed in degree zero, as an object of `DerivedQCoh`. -/
noncomputable def ofStructureSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    DerivedQCoh X :=
  ⟨(DerivedCategory.singleFunctor (Modules X) 0).obj
    (SheafOfModules.unit (structureSheaf X) : X.Modules),
    singleFunctor_unit_mem X⟩

/-- The underlying derived module of `ofStructureSheaf` is the unit `𝒪_X`-module in
degree zero. -/
theorem ofStructureSheaf_obj {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (ofStructureSheaf X).obj =
      (DerivedCategory.singleFunctor (Modules X) 0).obj
        (SheafOfModules.unit (structureSheaf X) : X.Modules) :=
  sorry

/-- Lemma 86.8.3 (1): if `Y` is affine and `f : X ⟶ Y` is a proper, flat morphism of
finite presentation, with `a` a right adjoint of `Rf_*` on `DerivedQCoh`, then
`a.obj (ofStructureSheaf Y)` is `Y`-perfect in `D(𝒪_X)`. -/
@[stacks 0E5V]
theorem rightAdjointStructureSheaf_isPerfectRelativeTo
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsAffine Y] [Proper f] [Flat f] [FinitePresentation f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a) :
    IsPerfectRelativeTo f (a.obj (ofStructureSheaf Y)).obj :=
  sorry

/-- Lemma 86.8.3 (2): if `Y` is affine and `f : X ⟶ Y` is a proper, flat morphism of
finite presentation, with `a` a right adjoint of `Rf_*` on `DerivedQCoh`, then
`Rf_* a(𝒪_Y)` has vanishing cohomology sheaves in every positive degree. -/
@[stacks 0E5V]
theorem rightAdjointStructureSheaf_pushforward_cohomology_isZero_of_pos
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsAffine Y] [Proper f] [Flat f] [FinitePresentation f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (i : ℤ) (hi : 0 < i) :
    IsZero
      (cohomologySheaf ((pushforwardCohomologyIn f).obj (a.obj (ofStructureSheaf Y))).obj i) :=
  sorry

/-- Lemma 86.8.3 (3): if `Y` is affine and `f : X ⟶ Y` is a proper, flat morphism of
finite presentation, with `a` a right adjoint of `Rf_*` on `DerivedQCoh`, then the
canonical map `𝒪_X ⟶ RHom(a(𝒪_Y), a(𝒪_Y))` is an isomorphism. -/
@[stacks 0E5V]
theorem rightAdjointStructureSheaf_homothety_isIso
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsAffine Y] [Proper f] [Flat f] [FinitePresentation f]
    [MonoidalCategory (ModuleDerived X)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (H : MonoidalClosed (ModuleDerived X)) :
    let ω := (a.obj (ofStructureSheaf Y)).obj
    IsIso (@MonoidalClosed.curry' (ModuleDerived X) _ _ ω ω (H.closed ω) (𝟙 ω)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
