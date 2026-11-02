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

lemma chartToField_naturality (σ : Spec (.of k) ⟶ S) (π : Y ⟶ ofOver (Over.mk σ))
    {U V : smallEtaleSite Y} (f : U ⟶ V) :
    f.left.left ≫ chartToField σ π V = chartToField σ π U := by
  have h : f.left ≫ ofOverPreimage (V.hom ≫ π) = ofOverPreimage (U.hom ≫ π) := by
    apply Yoneda.fullyFaithful.map_injective
    simp only [Functor.map_comp, ofOverPreimage, Functor.FullyFaithful.map_preimage]
    change (ofOverFunctor S).map f.left ≫ (V.hom ≫ π) = U.hom ≫ π
    rw [← Category.assoc, smallEtaleSite.w f]
    rfl
  exact congrArg (fun g ↦ g.left) h

/-- The field-to-sections ring map induced by the specified morphism to a field spectrum. -/
def scalar (σ : Spec (.of k) ⟶ S) (π : Y ⟶ ofOver (Over.mk σ))
    (chart : smallEtaleSite Y) : k →+* (structureSheaf Y).obj.obj (op chart) :=
  Scheme.Hom.globalSectionsMap (chartToField σ π chart)

lemma scalar_naturality (σ : Spec (.of k) ⟶ S) (π : Y ⟶ ofOver (Over.mk σ))
    {U V : smallEtaleSite Y} (f : U ⟶ V) (a : k) :
    (structureSheaf Y).obj.map f.op (scalar σ π V a) = scalar σ π U a := by
  have h := ΓSpec.adjunction.homEquiv_naturality_left_symm f.left.left (chartToField σ π V)
  have h' := congrArg (fun g ↦ g.unop.hom a) h
  change Scheme.Hom.globalSectionsMap (f.left.left ≫ chartToField σ π V) a =
    f.left.left.appTop (Scheme.Hom.globalSectionsMap (chartToField σ π V) a) at h'
  rw [chartToField_naturality σ π f] at h'
  exact h'.symm

/-- The additive sheaf underlying a module, lifted to a universe admitting sheafification. -/
def liftedAdditiveSheaf (G : Y.Modules) :
    Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} :=
  (sheafCompose (smallEtaleTopology Y) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
    ((SheafOfModules.toSheaf (structureSheaf Y)).obj G)

set_option backward.isDefEq.respectTransparency false in
/-- Multiplication by a field scalar on the additive sheaf of a module over a field spectrum. -/
@[no_expose] def scalarEndomorphism
    (σ : Spec (.of k) ⟶ S) (π : Y ⟶ ofOver (Over.mk σ)) (G : Y.Modules) (a : k) :
    (SheafOfModules.toSheaf (structureSheaf Y)).obj G ⟶
      (SheafOfModules.toSheaf (structureSheaf Y)).obj G where
  hom :=
    { app := fun chart ↦ AddCommGrpCat.ofHom
        (Module.toAddMonoidEnd ((structureSheaf Y).obj.obj chart) (G.val.obj chart)
          (scalar σ π chart.unop a))
      naturality := by
        intro U V f
        ext x
        letI : Module ((structureSheaf Y).obj.obj U)
            (((SheafOfModules.toSheaf (structureSheaf Y)).obj G).obj.obj U) :=
          (G.val.obj U).isModule
        change scalar σ π V.unop a • G.val.map f (x : G.val.obj U) =
          G.val.map f (scalar σ π U.unop a • (x : G.val.obj U))
        rw [G.val.map_smul]
        congr 1
        exact (scalar_naturality σ π f.unop a).symm }

set_option backward.isDefEq.respectTransparency false in
lemma scalarEndomorphism_add (σ : Spec (.of k) ⟶ S) (π : Y ⟶ ofOver (Over.mk σ))
    (G : Y.Modules) (a b : k) :
    scalarEndomorphism σ π G (a + b) =
      scalarEndomorphism σ π G a + scalarEndomorphism σ π G b := by
  ext chart x
  letI : Module ((structureSheaf Y).obj.obj chart)
      (((SheafOfModules.toSheaf (structureSheaf Y)).obj G).obj.obj chart) :=
    (G.val.obj chart).isModule
  change scalar σ π chart.unop (a + b) • (x : G.val.obj chart) =
    scalar σ π chart.unop a • (x : G.val.obj chart) +
      scalar σ π chart.unop b • (x : G.val.obj chart)
  rw [map_add, add_smul]

set_option backward.isDefEq.respectTransparency false in
lemma scalarEndomorphism_mul (σ : Spec (.of k) ⟶ S) (π : Y ⟶ ofOver (Over.mk σ))
    (G : Y.Modules) (a b : k) :
    scalarEndomorphism σ π G (a * b) =
      scalarEndomorphism σ π G b ≫ scalarEndomorphism σ π G a := by
  ext chart x
  letI : Module ((structureSheaf Y).obj.obj chart)
      (((SheafOfModules.toSheaf (structureSheaf Y)).obj G).obj.obj chart) :=
    (G.val.obj chart).isModule
  change scalar σ π chart.unop (a * b) • (x : G.val.obj chart) =
    scalar σ π chart.unop a • (scalar σ π chart.unop b • (x : G.val.obj chart))
  rw [map_mul, mul_smul]

set_option backward.isDefEq.respectTransparency false in
lemma scalarEndomorphism_one (σ : Spec (.of k) ⟶ S) (π : Y ⟶ ofOver (Over.mk σ))
    (G : Y.Modules) : scalarEndomorphism σ π G 1 = 𝟙 _ := by
  ext chart x
  letI : Module ((structureSheaf Y).obj.obj chart)
      (((SheafOfModules.toSheaf (structureSheaf Y)).obj G).obj.obj chart) :=
    (G.val.obj chart).isModule
  change scalar σ π chart.unop 1 • (x : G.val.obj chart) = x
  rw [map_one, one_smul]

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

set_option backward.isDefEq.respectTransparency false in
/-- The specified scalar action makes additive sheaf cohomology a module over the field. -/
@[implicit_reducible] def cohomologyModule (σ : Spec (.of k) ⟶ S) (π : Y ⟶ ofOver (Over.mk σ))
    (G : Y.Modules) (n : ℕ) :
    Module k (@Sheaf.H (smallEtaleSite Y) inferInstance (smallEtaleTopology Y)
      (liftedAdditiveSheaf G) inferInstance (HasExt.standard _) n) :=
  @Module.ofMinimalAxioms k _ inferInstance inferInstance (cohomologySMul σ π G n)
    (by
      intro a x y
      exact (@Sheaf.H.map.{u + 2, u + 1} (smallEtaleSite Y) inferInstance
        (smallEtaleTopology Y) inferInstance (HasExt.standard _)
        (liftedAdditiveSheaf G) (liftedAdditiveSheaf G)
        ((sheafCompose (smallEtaleTopology Y) AddCommGrpCat.uliftFunctor.{u + 1, u}).map
          (scalarEndomorphism σ π G a)) n).map_add x y)
    (by
      intro a b x
      letI : HasExt.{u + 2} (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :=
        HasExt.standard _
      letI : (sheafCompose (smallEtaleTopology Y)
          AddCommGrpCat.uliftFunctor.{u + 1, u}).Additive := by
        dsimp only [sheafCompose]
        infer_instance
      change @Sheaf.H.map.{u + 2, u + 1} (smallEtaleSite Y) inferInstance
        (smallEtaleTopology Y) inferInstance (HasExt.standard _)
        (liftedAdditiveSheaf G) (liftedAdditiveSheaf G)
        ((sheafCompose (smallEtaleTopology Y) AddCommGrpCat.uliftFunctor.{u + 1, u}).map
          (scalarEndomorphism σ π G (a + b))) n x = _
      rw [scalarEndomorphism_add, CategoryTheory.Functor.map_add,
        Sheaf.H.map_add_apply.{u + 2, u + 1} (J := smallEtaleTopology Y)]
      rfl)
    (by
      intro a b x
      letI : HasExt.{u + 2} (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :=
        HasExt.standard _
      change @Sheaf.H.map.{u + 2, u + 1} (smallEtaleSite Y) inferInstance
        (smallEtaleTopology Y) inferInstance (HasExt.standard _)
        (liftedAdditiveSheaf G) (liftedAdditiveSheaf G)
        ((sheafCompose (smallEtaleTopology Y) AddCommGrpCat.uliftFunctor.{u + 1, u}).map
          (scalarEndomorphism σ π G (a * b))) n x = _
      rw [scalarEndomorphism_mul, CategoryTheory.Functor.map_comp,
        Sheaf.H.map_comp_apply.{u + 2, u + 1} (J := smallEtaleTopology Y)]
      rfl)
    (by
      intro x
      letI : HasExt.{u + 2} (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :=
        HasExt.standard _
      change @Sheaf.H.map.{u + 2, u + 1} (smallEtaleSite Y) inferInstance
        (smallEtaleTopology Y) inferInstance (HasExt.standard _)
        (liftedAdditiveSheaf G) (liftedAdditiveSheaf G)
        ((sheafCompose (smallEtaleTopology Y) AddCommGrpCat.uliftFunctor.{u + 1, u}).map
          (scalarEndomorphism σ π G 1)) n x = x
      rw [scalarEndomorphism_one, CategoryTheory.Functor.map_id]
      exact Sheaf.H.map_id_apply.{u + 2, u + 1} (J := smallEtaleTopology Y)
        (F := liftedAdditiveSheaf G) x)

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
          (FieldFiber.scalarEndomorphism σ π G a)) n x := rfl

/-- The Euler characteristic of a module over a field spectrum is the alternating graded
Euler characteristic of its field-relative cohomology. -/
def fieldFiberEulerChar (σ : Spec (.of k) ⟶ S) (π : Y ⟶ ofOver (Over.mk σ))
    (G : Y.Modules) : ℤ :=
  GradedObject.eulerChar (ComplexShape.up ℕ) (fun n ↦ fieldCohomology σ π G n)

/-- Field-relative Euler characteristic is computed from the graded cohomology modules. -/
theorem fieldFiberEulerChar_eq (σ : Spec (.of k) ⟶ S) (π : Y ⟶ ofOver (Over.mk σ))
    (G : Y.Modules) :
    fieldFiberEulerChar σ π G =
      GradedObject.eulerChar (ComplexShape.up ℕ) (fun n ↦ fieldCohomology σ π G n) := rfl

end AlgebraicGeometry.AlgebraicSpace.Modules
