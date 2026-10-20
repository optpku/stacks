/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Basic
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Module.End
public import Mathlib.Algebra.Module.MinimalAxioms
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Homology.EulerCharacteristic

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {k : Type u} [Field k] {Y : AlgebraicSpace S}

namespace FieldFiber

/-- The scheme morphism from an étale chart to the specified field spectrum. -/
def chartToField (σ : Spec (.of k) ⟶ S) (π : Y ⟶ ofOver (Over.mk σ))
    (chart : smallEtaleSite Y) : chart.left.left ⟶ Spec (.of k) :=
  (ofOverPreimage (chart.hom ≫ π)).left

/-- The field-to-sections ring map induced by the specified morphism to a field spectrum. -/
def scalar (σ : Spec (.of k) ⟶ S) (π : Y ⟶ ofOver (Over.mk σ))
    (chart : smallEtaleSite Y) : k →+* (structureSheaf Y).obj.obj (op chart) :=
  Scheme.Hom.globalSectionsMap (chartToField σ π chart)

/-- The additive sheaf underlying a module, lifted to a universe admitting sheafification. -/
def liftedAdditiveSheaf (G : Y.Modules) :
    Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} :=
  (sheafCompose (smallEtaleTopology Y) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
    ((SheafOfModules.toSheaf (structureSheaf Y)).obj G)

/-- Multiplication by a field scalar on the additive sheaf of a module over a field spectrum. -/
@[no_expose] def scalarEndomorphism
    (σ : Spec (.of k) ⟶ S) (π : Y ⟶ ofOver (Over.mk σ)) (G : Y.Modules) (a : k) :
    (SheafOfModules.toSheaf (structureSheaf Y)).obj G ⟶
      (SheafOfModules.toSheaf (structureSheaf Y)).obj G where
  hom :=
    { app := fun chart ↦ AddCommGrpCat.ofHom
        (Module.toAddMonoidEnd ((structureSheaf Y).obj.obj chart) (G.val.obj chart)
          (scalar σ π chart.unop a))
      naturality := sorry }

/-- Field scalars act on additive sheaf cohomology by the induced scalar endomorphisms. -/
@[implicit_reducible] def cohomologySMul (σ : Spec (.of k) ⟶ S) (π : Y ⟶ ofOver (Over.mk σ))
    (G : Y.Modules) (n : ℕ) :
    SMul k (@Sheaf.H (smallEtaleSite Y) inferInstance (smallEtaleTopology Y)
      (liftedAdditiveSheaf G) inferInstance (HasExt.standard _) n) where
  smul a x :=
    @Sheaf.H.map.{u + 2, u + 1} (smallEtaleSite Y) inferInstance (smallEtaleTopology Y)
      inferInstance (HasExt.standard _) (liftedAdditiveSheaf G) (liftedAdditiveSheaf G)
      ((sheafCompose (smallEtaleTopology Y) AddCommGrpCat.uliftFunctor.{u + 1, u}).map
        (scalarEndomorphism σ π G a)) n x

/-- The specified scalar action makes additive sheaf cohomology a module over the field. -/
@[implicit_reducible] def cohomologyModule (σ : Spec (.of k) ⟶ S) (π : Y ⟶ ofOver (Over.mk σ))
    (G : Y.Modules) (n : ℕ) :
    Module k (@Sheaf.H (smallEtaleSite Y) inferInstance (smallEtaleTopology Y)
      (liftedAdditiveSheaf G) inferInstance (HasExt.standard _) n) :=
  @Module.ofMinimalAxioms k _ inferInstance inferInstance (cohomologySMul σ π G n)
    sorry sorry sorry sorry

end FieldFiber

/-- Cohomology of a module over a field spectrum, with the scalar action induced by its
specified structure morphism. -/
def fieldCohomology (σ : Spec (.of k) ⟶ S) (π : Y ⟶ ofOver (Over.mk σ))
    (G : Y.Modules) (n : ℕ) : ModuleCat.{u + 2} k :=
  @ModuleCat.of k inferInstance
    (@Sheaf.H (smallEtaleSite Y) inferInstance (smallEtaleTopology Y)
      (FieldFiber.liftedAdditiveSheaf G) inferInstance (HasExt.standard _) n)
    inferInstance (FieldFiber.cohomologyModule σ π G n)

/-- Scalar multiplication on field-relative cohomology is the map on sheaf cohomology
induced by multiplication on the underlying additive sheaf. -/
theorem fieldCohomology_smul (σ : Spec (.of k) ⟶ S) (π : Y ⟶ ofOver (Over.mk σ))
    (G : Y.Modules) (n : ℕ) (a : k) (x : fieldCohomology σ π G n) :
    a • x =
      @Sheaf.H.map.{u + 2, u + 1} (smallEtaleSite Y) inferInstance (smallEtaleTopology Y)
        inferInstance (HasExt.standard _)
        (FieldFiber.liftedAdditiveSheaf G) (FieldFiber.liftedAdditiveSheaf G)
        ((sheafCompose (smallEtaleTopology Y) AddCommGrpCat.uliftFunctor.{u + 1, u}).map
          (FieldFiber.scalarEndomorphism σ π G a)) n x := sorry

/-- The Euler characteristic of a module over a field spectrum is the alternating graded
Euler characteristic of its field-relative cohomology. -/
def fieldFiberEulerChar (σ : Spec (.of k) ⟶ S) (π : Y ⟶ ofOver (Over.mk σ))
    (G : Y.Modules) : ℤ :=
  GradedObject.eulerChar (ComplexShape.up ℕ) (fun n ↦ fieldCohomology σ π G n)

/-- Field-relative Euler characteristic is computed from the graded cohomology modules. -/
theorem fieldFiberEulerChar_eq (σ : Spec (.of k) ⟶ S) (π : Y ⟶ ofOver (Over.mk σ))
    (G : Y.Modules) :
    fieldFiberEulerChar σ π G =
      GradedObject.eulerChar (ComplexShape.up ℕ) (fun n ↦ fieldCohomology σ π G n) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
