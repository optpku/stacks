/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Cohomology
public import stacks_project.Chap85.Definition_85_12_1_Cartesian
public import stacks_project.Chap85.Lemma_85_11_1_Flat

/-!
# Lemma 85.12.8

In Situation 85.3.3, an object of `D(C_total)` is cartesian if and only if every
homology sheaf is a cartesian abelian sheaf. If `O` is a sheaf of rings on
`C_total` whose coface maps of ringed topoi are flat, the same homology
criterion holds in `D(O)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [IsMorphismDiagram C J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (f : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map f).toFunctor).op.HasLeftKanExtension P]

section Abelian

variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (f : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map f).toFunctor).op.HasLeftKanExtension P]

section AbelianDerived

variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]

/-- Lemma 85.12.8 (1)
In Situation 85.3.3, an object `K` of `D(C_total)` is cartesian if and only if
every homology sheaf `(DerivedCategory.homologyFunctor _ q).obj K` is a
cartesian abelian sheaf. -/
@[stacks 0D7L]
theorem AbelianDerived.isCartesian_iff_homology
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) :
    AbelianDerived.IsCartesian C J K ↔
      ∀ q : ℤ, Abelian.IsCartesian C J
        ((DerivedCategory.homologyFunctor
          (Sheaf (topology C J) AddCommGrpCat.{w}) q).obj K) :=
  sorry

/-- The degree-`q` homology sheaf of a cartesian object of `D(C_total)` is cartesian. -/
instance AbelianDerived.instHomology_isCartesian
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    [AbelianDerived.IsCartesian C J K] (q : ℤ) :
    Abelian.IsCartesian C J
      ((DerivedCategory.homologyFunctor
        (Sheaf (topology C J) AddCommGrpCat.{w}) q).obj K) :=
  sorry

/-- An object of `D(C_total)` whose homology sheaves are all cartesian is cartesian. -/
instance AbelianDerived.instIsCartesian_of_homology
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    [∀ q : ℤ, Abelian.IsCartesian C J
      ((DerivedCategory.homologyFunctor
        (Sheaf (topology C J) AddCommGrpCat.{w}) q).obj K)] :
    AbelianDerived.IsCartesian C J K :=
  sorry

end AbelianDerived

end Abelian

section Modules

variable [IsMorphismDiagram C J]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (f : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O f).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (stageMorphism C J O n)]
variable [∀ {m n : SimplexCategory} (f : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O f)]

/-- Lemma 85.12.8 (2)
In Situation 85.3.3, if `O` is a sheaf of rings on `C_total` such that each coface
morphism `ringedToposMap C J O (SimplexCategory.δ j)` of ringed topoi is flat,
then an object `K` of `D(O)` is cartesian if and only if every cohomology sheaf
`Hom.ModuleDerived.cohomologySheaf (totalRingedSite C J O) K q` is a cartesian
`O`-module. -/
@[stacks 0D7L]
theorem ModuleDerived.isCartesian_iff_homology
    (h_flat : ∀ {n : ℕ} (j : Fin (n + 2)),
      ToposHom.IsFlat (ringedToposMap C J O (SimplexCategory.δ j)))
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J O)) :
    ModuleDerived.IsCartesian C J O K ↔
      ∀ q : ℤ, Module.IsCartesian C J O
        (Hom.ModuleDerived.cohomologySheaf (totalRingedSite C J O) K q) :=
  sorry

/-- Under coface flatness, the degree-`q` cohomology sheaf of a cartesian object of
`D(O)` is a cartesian `O`-module. -/
theorem ModuleDerived.homology_isCartesian
    (h_flat : ∀ {n : ℕ} (j : Fin (n + 2)),
      ToposHom.IsFlat (ringedToposMap C J O (SimplexCategory.δ j)))
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J O))
    [ModuleDerived.IsCartesian C J O K] (q : ℤ) :
    Module.IsCartesian C J O
      (Hom.ModuleDerived.cohomologySheaf (totalRingedSite C J O) K q) :=
  sorry

/-- Under coface flatness, an object of `D(O)` whose cohomology sheaves are all
cartesian `O`-modules is cartesian. -/
theorem ModuleDerived.isCartesian_of_homology
    (h_flat : ∀ {n : ℕ} (j : Fin (n + 2)),
      ToposHom.IsFlat (ringedToposMap C J O (SimplexCategory.δ j)))
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J O))
    (hK : ∀ q : ℤ, Module.IsCartesian C J O
      (Hom.ModuleDerived.cohomologySheaf (totalRingedSite C J O) K q)) :
    ModuleDerived.IsCartesian C J O K :=
  sorry

end Modules

end CategoryTheory.SimplicialSites
