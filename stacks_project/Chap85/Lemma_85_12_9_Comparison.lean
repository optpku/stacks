/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Monoidal.Braided.Transport
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed
public import ReasLib.Algebra.Homology.DerivedCategory.Adjunction
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.Monoidal.Adjunction.ProjectionFormula
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.Monoidal.Continuous
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Integer
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import stacks_project.Chap85.Definition_85_12_1_Cartesian
public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek

/-!
# Canonical shriek-tensor comparisons on a simplicial site

In Situation 85.3.3, exactness of `g_{n!}` supplies derived functors adjoint to
stage restriction. The comparison `g_{n!} K_n ⟶ g_{n!} ℤ ⊗ᴸ K` is the derived
adjunct of the unit-tensor map on `K_n`, and likewise for modules after
flatness of `f_φ⁻¹ O_n ⟶ O_m`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open Functor
open RingedSite
open ComplexShape
open CategoryTheory.DerivedCategory

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [IsMorphismDiagram C J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasPointwiseLeftKanExtension P]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget AddCommGrpCat.{w})]

/-- The `⊗_ℤ` monoidal structure on `AddCommGrpCat`, transported from `ModuleCat (ULift ℤ)`.
This is a named value rather than a global instance, so it does not diamond with the
cartesian monoidal structure. -/
@[implicit_reducible]
def addCommGrpCatTensorMonoidal : MonoidalCategory AddCommGrpCat.{w} :=
  CategoryTheory.Monoidal.transport <|
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        (ULift.ringEquiv : ULift.{w} ℤ ≃+* ℤ)).symm.trans
      (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}).asEquivalence

-- Local instance justification (defeq pin): sheaf tensors, `W.IsMonoidal`, and the
-- coefficient tensor unit read the `⊗_ℤ` structure; the cartesian instance on
-- `AddCommGrpCat` is not `⊗_ℤ`. A file-local pin is required because `W.IsMonoidal`
-- appears in instance types, where a body-only `letI` does not elaborate.
attribute [local instance] addCommGrpCatTensorMonoidal

/-- Weak equivalences on the total site are monoidal for the pinned `⊗_ℤ`. -/
instance abelianTotalW_isMonoidal :
    ((topology C J).W : MorphismProperty ((totalSite C)ᵒᵖ ⥤ AddCommGrpCat.{w})).IsMonoidal :=
  sorry

/-- Weak equivalences on the degree-`n` site are monoidal for the pinned `⊗_ℤ`. -/
instance abelianStageW_isMonoidal (n : SimplexCategory) :
    (((J n).toGrothendieck).W :
      MorphismProperty ((C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w})).IsMonoidal :=
  sorry

/-- The `ℤ`-tensor monoidal structure on abelian sheaves on `C_total`. -/
instance abelianSheaf_monoidalCategory :
    MonoidalCategory (Sheaf (topology C J) AddCommGrpCat.{w}) :=
  -- Local instance justification (defeq pin): `Sheaf.monoidalCategory` reads the coefficient
  -- monoidal structure; the cartesian instance on `AddCommGrpCat` is not `⊗_ℤ`.
  letI := addCommGrpCatTensorMonoidal
  Sheaf.monoidalCategory (topology C J) AddCommGrpCat.{w}

/-- The `ℤ`-tensor monoidal structure on abelian sheaves on the degree-`n` site. -/
instance abelianSheaf_monoidalCategory_stage (n : SimplexCategory) :
    MonoidalCategory (Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w}) :=
  -- Local instance justification (defeq pin): `Sheaf.monoidalCategory` reads the coefficient
  -- monoidal structure; the cartesian instance on `AddCommGrpCat` is not `⊗_ℤ`.
  letI := addCommGrpCatTensorMonoidal
  Sheaf.monoidalCategory ((J n).toGrothendieck) AddCommGrpCat.{w}

/-- Tensor of abelian sheaves on `C_total` is additive in each variable. -/
instance abelianSheaf_monoidalPreadditive :
    MonoidalPreadditive (Sheaf (topology C J) AddCommGrpCat.{w}) :=
  sorry

/-- Tensor of abelian sheaves on the degree-`n` site is additive in each variable. -/
instance abelianSheaf_monoidalPreadditive_stage (n : SimplexCategory) :
    MonoidalPreadditive (Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w}) :=
  sorry

/-- The constant sheaf with value `ULift ℤ` on the degree-`n` site. -/
abbrev constantInteger (n : SimplexCategory) :
    Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w} :=
  constantIntegerSheaf (J n).toGrothendieck

/-- Unfolding `constantInteger` recovers `constantIntegerSheaf` on the stage topology. -/
theorem constantInteger_eq (n : SimplexCategory) :
    constantInteger C J n = constantIntegerSheaf (J n).toGrothendieck :=
  sorry

/-- Identification of `ULift ℤ` with the transported `⊗_ℤ` unit of `AddCommGrpCat`. -/
def uliftIntegerIsoTensorUnit :
    AddCommGrpCat.of (ULift.{w} ℤ) ≅ 𝟙_ AddCommGrpCat.{w} :=
  Iso.refl _

/-- For the pinned `ℤ`-tensor, the monoidal unit on the degree-`n` site is the constant
integer sheaf. -/
def constantIntegerIsoTensorUnit (n : SimplexCategory) :
    constantInteger C J n ≅ 𝟙_ (Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w}) :=
  (constantSheaf ((J n).toGrothendieck) AddCommGrpCat.{w}).mapIso
    (uliftIntegerIsoTensorUnit)

/-- Unfolding `constantIntegerIsoTensorUnit` recovers the constant-sheaf image of
`uliftIntegerIsoTensorUnit`. -/
theorem constantIntegerIsoTensorUnit_eq (n : SimplexCategory) :
    constantIntegerIsoTensorUnit C J n =
      (constantSheaf ((J n).toGrothendieck) AddCommGrpCat.{w}).mapIso
        (uliftIntegerIsoTensorUnit) :=
  sorry

/-- Stage restriction `g_n⁻¹` is strong monoidal for the pinned `ℤ`-tensors. -/
instance abelianStageRestrict_monoidal (n : SimplexCategory) :
    (component C J AddCommGrpCat.{w} n).Monoidal :=
  (ofStage C n).sheafPushforwardContinuousMonoidal

/-- The canonical oplax monoidal comparison on abelian lower shriek, as the left adjoint of
the strong monoidal restriction functor. -/
instance abelianLowerShriek_oplaxMonoidal (n : SimplexCategory) :
    (abelianLowerShriek C J n).OplaxMonoidal :=
  (abelianLowerShriek_adjunction C J n).leftAdjointOplaxMonoidal

/-- Abelian lower shriek `g_{n!}` preserves finite limits, by exactness in Lemma 85.3.5. -/
instance abelianLowerShriek_preservesFiniteLimits (n : SimplexCategory) :
    PreservesFiniteLimits (abelianLowerShriek C J n) :=
  sorry

/-- Abelian lower shriek `g_{n!}` preserves finite colimits, by exactness in Lemma 85.3.5. -/
instance abelianLowerShriek_preservesFiniteColimits (n : SimplexCategory) :
    PreservesFiniteColimits (abelianLowerShriek C J n) :=
  sorry

/-- Derived abelian lower shriek `g_{n!}` on `D(C_n)`. -/
def abelianLowerShriekDerived (n : SimplexCategory) :
    DerivedCategory (Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w}) ⥤
      DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}) :=
  (abelianLowerShriek C J n).mapDerivedCategory

/-- `abelianLowerShriekDerived n` is `mapDerivedCategory` of abelian lower shriek. -/
theorem abelianLowerShriekDerived_eq (n : SimplexCategory) :
    abelianLowerShriekDerived C J n = (abelianLowerShriek C J n).mapDerivedCategory :=
  sorry

/-- The derived adjunction `g_{n!} ⊣ g_n⁻¹` induced by exactness of both functors. -/
def derivedLowerShriekAdjunction (n : SimplexCategory) :
    abelianLowerShriekDerived C J n ⊣ derivedComponent C J n :=
  Adjunction.mapDerivedCategory (abelianLowerShriek_adjunction C J n)

/-- `derivedLowerShriekAdjunction` is `Adjunction.mapDerivedCategory` of abelian lower shriek. -/
theorem derivedLowerShriekAdjunction_eq (n : SimplexCategory) :
    derivedLowerShriekAdjunction C J n =
      Adjunction.mapDerivedCategory (abelianLowerShriek_adjunction C J n) :=
  sorry

/-- The unit object `ℤ` of `D(C_n)`, as the constant integer sheaf in degree zero. -/
def derivedConstantInteger (n : SimplexCategory) :
    DerivedCategory (Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w}) :=
  (DerivedCategory.singleFunctor _ 0).obj (constantInteger C J n)

/-- `derivedConstantInteger n` is the degree-zero placement of `constantInteger`. -/
theorem derivedConstantInteger_eq (n : SimplexCategory) :
    derivedConstantInteger C J n =
      (DerivedCategory.singleFunctor _ 0).obj (constantInteger C J n) :=
  sorry

/-- Bundled exact abelian lower shriek. -/
def abelianLowerShriekExact (n : SimplexCategory) :
    Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w} ⥤ₑ
      Sheaf (topology C J) AddCommGrpCat.{w} :=
  ExactFunctor.of (abelianLowerShriek C J n)

/-- Exactness identifies `D(g_n⁻¹ ⋙ g_{n!})` with `g_{n!}` after `K ↦ K_n`. -/
def derivedShriekCompIso (n : SimplexCategory) :
    (component C J AddCommGrpCat.{w} n ⋙ abelianLowerShriek C J n).mapDerivedCategory ≅
      derivedComponent C J n ⋙ abelianLowerShriekDerived C J n :=
  ExactFunctor.MapDerivedCategory.compFunctorIso
    (derivedComponentExact C J n) (abelianLowerShriekExact C J n)

/-- The sheaf-level comparison `g_{n!} F_n ⟶ g_{n!} ℤ ⊗ F`, as the projection-formula
map of `g_{n!} ⊣ g_n⁻¹` on the constant integer sheaf, after the left unitor on `F_n`. -/
def abelianShriekTensorHom (n : SimplexCategory)
    (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    (abelianLowerShriek C J n).obj ((component C J AddCommGrpCat.{w} n).obj F) ⟶
      (abelianLowerShriek C J n).obj (constantInteger C J n) ⊗ F :=
  (abelianLowerShriek C J n).map
      ((MonoidalCategory.leftUnitor
          ((component C J AddCommGrpCat.{w} n).obj F)).inv ≫
        ((constantIntegerIsoTensorUnit C J n).inv ⊗ₘ
          𝟙 ((component C J AddCommGrpCat.{w} n).obj F))) ≫
    (abelianLowerShriek_adjunction C J n).projectionFormulaMapOf
      (fun X Y ↦ Functor.OplaxMonoidal.δ (abelianLowerShriek C J n) X Y)
      (constantInteger C J n) F

/-- `abelianShriekTensorHom` is the left-unitor composite of the projection-formula map
on the constant integer sheaf. -/
theorem abelianShriekTensorHom_eq (n : SimplexCategory)
    (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    abelianShriekTensorHom C J n F =
      (abelianLowerShriek C J n).map
          ((MonoidalCategory.leftUnitor
              ((component C J AddCommGrpCat.{w} n).obj F)).inv ≫
            ((constantIntegerIsoTensorUnit C J n).inv ⊗ₘ
              𝟙 ((component C J AddCommGrpCat.{w} n).obj F))) ≫
        (abelianLowerShriek_adjunction C J n).projectionFormulaMapOf
          (fun X Y ↦ Functor.OplaxMonoidal.δ (abelianLowerShriek C J n) X Y)
          (constantInteger C J n) F :=
  sorry

/-- The sheaf-level adjunct of `abelianShriekTensorHom`, as the left-unitor composite of
the adjunction unit at `ℤ` tensored with `F_n`, followed by the strong-monoidal comparison
of `g_n⁻¹`. -/
def abelianShriekTensorMate (n : SimplexCategory)
    (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    (component C J AddCommGrpCat.{w} n).obj F ⟶
      (component C J AddCommGrpCat.{w} n).obj
        ((abelianLowerShriek C J n).obj (constantInteger C J n) ⊗ F) :=
  (MonoidalCategory.leftUnitor
      ((component C J AddCommGrpCat.{w} n).obj F)).inv ≫
    ((constantIntegerIsoTensorUnit C J n).inv ⊗ₘ
      𝟙 ((component C J AddCommGrpCat.{w} n).obj F)) ≫
    ((abelianLowerShriek_adjunction C J n).unit.app (constantInteger C J n) ⊗ₘ
      𝟙 ((component C J AddCommGrpCat.{w} n).obj F)) ≫
    LaxMonoidal.μ (component C J AddCommGrpCat.{w} n)
      ((abelianLowerShriek C J n).obj (constantInteger C J n)) F

/-- `abelianShriekTensorHom` is the adjunct of the independent unit-tensor-μ mate. -/
theorem abelianShriekTensorHom_spec (n : SimplexCategory)
    (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    abelianShriekTensorHom C J n F =
      ((abelianLowerShriek_adjunction C J n).homEquiv
          ((component C J AddCommGrpCat.{w} n).obj F)
          ((abelianLowerShriek C J n).obj (constantInteger C J n) ⊗ F)).symm
        (abelianShriekTensorMate C J n F) :=
  sorry

/-- The natural transformation whose components are `abelianShriekTensorMate`. -/
def abelianShriekTensorMateNatTrans (n : SimplexCategory) :
    component C J AddCommGrpCat.{w} n ⟶
      tensorLeft ((abelianLowerShriek C J n).obj (constantInteger C J n)) ⋙
        component C J AddCommGrpCat.{w} n where
  app F := abelianShriekTensorMate C J n F
  naturality := sorry

/-- The natural transformation of abelian sheaves whose components are `abelianShriekTensorHom`. -/
def abelianShriekTensorNatTrans (n : SimplexCategory) :
    component C J AddCommGrpCat.{w} n ⋙ abelianLowerShriek C J n ⟶
      tensorLeft ((abelianLowerShriek C J n).obj (constantInteger C J n)) where
  app F := abelianShriekTensorHom C J n F
  naturality := sorry

/-- Tensoring over `ℤ` with `g_{n!} ℤ` is additive. -/
instance abelianShriekInteger_tensorLeft_additive (n : SimplexCategory) :
    (tensorLeft ((abelianLowerShriek C J n).obj (constantInteger C J n))).Additive :=
  inferInstance

/-- Tensoring over `ℤ` with `g_{n!} ℤ` preserves finite colimits. -/
instance abelianShriekInteger_tensorLeft_preservesFiniteColimits (n : SimplexCategory) :
    PreservesFiniteColimits
      (tensorLeft ((abelianLowerShriek C J n).obj (constantInteger C J n))) :=
  sorry

/-- Tensoring over `ℤ` with `g_{n!} ℤ` preserves finite limits, since `g_{n!} ℤ` is a
coproduct of copies of `ℤ` and hence flat. -/
instance abelianShriekInteger_tensorLeft_preservesFiniteLimits (n : SimplexCategory) :
    PreservesFiniteLimits
      (tensorLeft ((abelianLowerShriek C J n).obj (constantInteger C J n))) :=
  sorry

/-- Derived tensoring on the left by `g_{n!} ℤ`, as `mapDerivedCategory` of the exact
underived tensor. -/
def abelianShriekIntegerTensorDerived (n : SimplexCategory) :
    DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}) ⥤
      DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}) :=
  (tensorLeft ((abelianLowerShriek C J n).obj (constantInteger C J n))).mapDerivedCategory

/-- The localization-lift of `abelianShriekTensorNatTrans`. -/
def derivedShriekTensorComparisonComposite (n : SimplexCategory)
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) :
    ((component C J AddCommGrpCat.{w} n ⋙
        abelianLowerShriek C J n).mapDerivedCategory).obj K ⟶
      (abelianShriekIntegerTensorDerived C J n).obj K :=
  (Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (up ℤ))
      ((component C J AddCommGrpCat.{w} n ⋙
          abelianLowerShriek C J n).mapHomologicalComplex (up ℤ) ⋙
        DerivedCategory.Q)
      ((tensorLeft ((abelianLowerShriek C J n).obj (constantInteger C J n))).mapHomologicalComplex
        (up ℤ) ⋙ DerivedCategory.Q)
      (component C J AddCommGrpCat.{w} n ⋙ abelianLowerShriek C J n).mapDerivedCategory
      (tensorLeft ((abelianLowerShriek C J n).obj (constantInteger C J n))).mapDerivedCategory
      (whiskerRight
        (NatTrans.mapHomologicalComplex (abelianShriekTensorNatTrans C J n) (up ℤ))
        DerivedCategory.Q)).app K

/-- The canonical comparison `g_{n!} K_n ⟶ g_{n!} ℤ ⊗ K`, as the derived functor of exact
tensoring with `g_{n!} ℤ`. -/
def derivedShriekTensorComparison (n : SimplexCategory)
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) :
    (abelianLowerShriekDerived C J n).obj ((derivedComponent C J n).obj K) ⟶
      (abelianShriekIntegerTensorDerived C J n).obj K :=
  (derivedShriekCompIso C J n).inv.app K ≫
    derivedShriekTensorComparisonComposite C J n K

/-- The derived adjunct of `derivedShriekTensorComparison`, as the left-unitor composite of
the adjunction unit at `ℤ` tensored with `K_n`, followed by the strong-monoidal comparison
of `g_n⁻¹`. -/
def derivedShriekTensorMate (n : SimplexCategory)
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) :
    (derivedComponent C J n).obj K ⟶
      (derivedComponent C J n).obj ((abelianShriekIntegerTensorDerived C J n).obj K) :=
  (Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (up ℤ))
      ((component C J AddCommGrpCat.{w} n).mapHomologicalComplex (up ℤ) ⋙
        DerivedCategory.Q)
      ((tensorLeft ((abelianLowerShriek C J n).obj (constantInteger C J n)) ⋙
          component C J AddCommGrpCat.{w} n).mapHomologicalComplex (up ℤ) ⋙
        DerivedCategory.Q)
      (component C J AddCommGrpCat.{w} n).mapDerivedCategory
      (tensorLeft ((abelianLowerShriek C J n).obj (constantInteger C J n)) ⋙
        component C J AddCommGrpCat.{w} n).mapDerivedCategory
      (whiskerRight
        (NatTrans.mapHomologicalComplex (abelianShriekTensorMateNatTrans C J n) (up ℤ))
        DerivedCategory.Q)).app K ≫
    (ExactFunctor.MapDerivedCategory.compFunctorIso
        (ExactFunctor.of
          (tensorLeft ((abelianLowerShriek C J n).obj (constantInteger C J n))))
        (derivedComponentExact C J n)).hom.app K

/-- `derivedShriekTensorComparison` is the derived adjunct of the left-unitor composite of
the adjunction unit at `ℤ` tensored with `K_n`. -/
theorem derivedShriekTensorComparison_spec (n : SimplexCategory)
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) :
    derivedShriekTensorComparison C J n K =
      ((derivedLowerShriekAdjunction C J n).homEquiv
          ((derivedComponent C J n).obj K)
          ((abelianShriekIntegerTensorDerived C J n).obj K)).symm
        (derivedShriekTensorMate C J n K) :=
  sorry

section ModuleShriek

variable (R : Sheaf (topology C J) RingCat.{w})

/-- Module inverse image along the degree-`n` inclusion. -/
abbrev moduleInverseImage (n : SimplexCategory) :
    SheafOfModules.{w} R ⥤ SheafOfModules.{w} (componentRingSheaf C J R n) :=
  Cocontinuous.moduleInverseImage (ofStage C n) R

/-- `moduleInverseImage` is ReasLib inverse image along `ofStage C n`. -/
theorem moduleInverseImage_eq (n : SimplexCategory) :
    moduleInverseImage C J R n = Cocontinuous.moduleInverseImage (ofStage C n) R :=
  sorry

end ModuleShriek

section Modules

variable (O : Sheaf (topology C J) CommRingCat.{w})
variable [(topology C J).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose
    (forget₂ CommRingCat.{w} RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J (Sheaf.ringSheafOfComm O) n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J (Sheaf.ringSheafOfComm O) φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived
    (stageMorphism C J (Sheaf.ringSheafOfComm O) n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived
      (ringedToposMap C J (Sheaf.ringSheafOfComm O) φ)]
variable [(topology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Canonical tensor product on modules over the commutative ring sheaf `O`. -/
instance totalModules_monoidalCategory :
    MonoidalCategory (SheafOfModules.{w} (Sheaf.ringSheafOfComm O)) :=
  SheafOfModules.RingedSite.moduleMonoidalCategory O

/-- Tensor of `O`-modules is additive in both variables. -/
instance totalModules_monoidalPreadditive :
    MonoidalPreadditive (SheafOfModules.{w} (Sheaf.ringSheafOfComm O)) :=
  SheafOfModules.RingedSite.monoidalPreadditive

/-- Canonical tensor product on modules over `O_n`. -/
instance componentModules_monoidalCategory (n : SimplexCategory) :
    MonoidalCategory
      (SheafOfModules.{w} (componentRingSheaf C J (Sheaf.ringSheafOfComm O) n)) :=
  SheafOfModules.RingedSite.moduleMonoidalCategory
    ((component C J CommRingCat.{w} n).obj O)

/-- Tensor of `O_n`-modules is additive in both variables. -/
instance componentModules_monoidalPreadditive (n : SimplexCategory) :
    MonoidalPreadditive
      (SheafOfModules.{w} (componentRingSheaf C J (Sheaf.ringSheafOfComm O) n)) :=
  sorry

variable [∀ n,
    (moduleInverseImage C J (Sheaf.ringSheafOfComm O) n).Monoidal]

/-- Module lower shriek `g_{n!}` along the degree-`n` inclusion, as a typed ReasLib
specialization so the source topology of `ofStage` is not a metavariable. -/
abbrev stageModuleLowerShriek (n : SimplexCategory) :
    SheafOfModules.{w} (componentRingSheaf C J (Sheaf.ringSheafOfComm O) n) ⥤
      SheafOfModules.{w} (Sheaf.ringSheafOfComm O) :=
  Cocontinuous.moduleLowerShriek (ofStage C n) (Sheaf.ringSheafOfComm O)

/-- Unfolding `stageModuleLowerShriek` recovers ReasLib lower shriek along `ofStage`. -/
theorem stageModuleLowerShriek_eq (n : SimplexCategory) :
    stageModuleLowerShriek C J O n =
      Cocontinuous.moduleLowerShriek (ofStage C n) (Sheaf.ringSheafOfComm O) :=
  sorry

/-- The canonical adjunction `g_{n!} ⊣ g_n^*` on `O`-modules. -/
def stageModuleLowerShriekAdjunction (n : SimplexCategory) :
    stageModuleLowerShriek C J O n ⊣
      moduleInverseImage C J (Sheaf.ringSheafOfComm O) n :=
  Cocontinuous.moduleLowerShriek.adjunction (ofStage C n) (Sheaf.ringSheafOfComm O)

/-- `stageModuleLowerShriekAdjunction` is the ReasLib lower-shriek adjunction along `ofStage`. -/
theorem stageModuleLowerShriekAdjunction_eq (n : SimplexCategory) :
    stageModuleLowerShriekAdjunction C J O n =
      Cocontinuous.moduleLowerShriek.adjunction (ofStage C n) (Sheaf.ringSheafOfComm O) :=
  sorry

/-- Module lower shriek `g_{n!}` is additive. -/
instance moduleLowerShriek_additive (n : SimplexCategory) :
    (stageModuleLowerShriek C J O n).Additive :=
  sorry

/-- The canonical oplax monoidal comparison on module lower shriek, as the left adjoint of
strong monoidal inverse image. -/
instance moduleLowerShriek_oplaxMonoidal (n : SimplexCategory) :
    (stageModuleLowerShriek C J O n).OplaxMonoidal :=
  (stageModuleLowerShriekAdjunction C J O n).leftAdjointOplaxMonoidal

/-- Exactness of `g_{n!}` on `O`-modules, from Lemma 85.6.3, after the source flatness
hypothesis on every simplex operator. -/
theorem moduleLowerShriek_preservesFiniteLimits
    (h_flat : ∀ {n m : SimplexCategory} (φ : n ⟶ m),
      ToposHom.IsFlat (ringedToposMap C J (Sheaf.ringSheafOfComm O) φ))
    (n : SimplexCategory) :
    PreservesFiniteLimits (stageModuleLowerShriek C J O n) :=
  sorry

/-- Colimit-preservation of `g_{n!}` on `O`-modules, from Lemma 85.6.3. -/
theorem moduleLowerShriek_preservesFiniteColimits
    (h_flat : ∀ {n m : SimplexCategory} (φ : n ⟶ m),
      ToposHom.IsFlat (ringedToposMap C J (Sheaf.ringSheafOfComm O) φ))
    (n : SimplexCategory) :
    PreservesFiniteColimits (stageModuleLowerShriek C J O n) :=
  sorry

/-- Derived module lower shriek `g_{n!}` on `D(O_n)`, using exactness from `h_flat`. -/
def moduleLowerShriekDerived
    (h_flat : ∀ {n m : SimplexCategory} (φ : n ⟶ m),
      ToposHom.IsFlat (ringedToposMap C J (Sheaf.ringSheafOfComm O) φ))
    (n : SimplexCategory) :
    Hom.ModuleDerived.{w} (componentRingedSite C J (Sheaf.ringSheafOfComm O) n) ⥤
      Hom.ModuleDerived.{w} (totalRingedSite C J (Sheaf.ringSheafOfComm O)) :=
  -- Local instance justification (proof-local temporary data): Lemma 85.6.3 supplies exactness of
  -- `g_{n!}` only after the source flatness hypothesis `h_flat`.
  letI := moduleLowerShriek_preservesFiniteLimits C J O h_flat n
  letI := moduleLowerShriek_preservesFiniteColimits C J O h_flat n
  (stageModuleLowerShriek C J O n).mapDerivedCategory

/-- `moduleLowerShriekDerived` is `mapDerivedCategory` of Lemma 85.6.1 module lower shriek. -/
theorem moduleLowerShriekDerived_eq
    (h_flat : ∀ {n m : SimplexCategory} (φ : n ⟶ m),
      ToposHom.IsFlat (ringedToposMap C J (Sheaf.ringSheafOfComm O) φ))
    (n : SimplexCategory)
    [PreservesFiniteLimits (stageModuleLowerShriek C J O n)]
    [PreservesFiniteColimits (stageModuleLowerShriek C J O n)] :
    moduleLowerShriekDerived C J O h_flat n =
      (stageModuleLowerShriek C J O n).mapDerivedCategory :=
  sorry

/-- The unit object `O_n` of `D(O_n)`, as the structure sheaf in degree zero. -/
def moduleDerivedUnit (n : SimplexCategory) :
    Hom.ModuleDerived.{w} (componentRingedSite C J (Sheaf.ringSheafOfComm O) n) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (SheafOfModules.unit (componentRingSheaf C J (Sheaf.ringSheafOfComm O) n))

/-- `moduleDerivedUnit n` is the degree-zero placement of the structure sheaf `O_n`. -/
theorem moduleDerivedUnit_eq (n : SimplexCategory) :
    moduleDerivedUnit C J O n =
      (DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (componentRingSheaf C J (Sheaf.ringSheafOfComm O) n)) :=
  sorry

/-- Inverse image `g_n^*` from the lower-shriek adjunction is additive. -/
instance moduleInverseImage_additive (n : SimplexCategory) :
    (moduleInverseImage C J (Sheaf.ringSheafOfComm O) n).Additive :=
  sorry

/-- Inverse image `g_n^*` preserves finite limits. -/
instance moduleInverseImage_preservesFiniteLimits (n : SimplexCategory) :
    PreservesFiniteLimits
      (moduleInverseImage C J (Sheaf.ringSheafOfComm O) n) :=
  sorry

/-- Inverse image `g_n^*` preserves finite colimits. -/
instance moduleInverseImage_preservesFiniteColimits (n : SimplexCategory) :
    PreservesFiniteColimits
      (moduleInverseImage C J (Sheaf.ringSheafOfComm O) n) :=
  sorry

/-- The derived adjunction `g_{n!} ⊣ g_n^*` on modules, after the source flatness
hypothesis. -/
def moduleDerivedLowerShriekAdjunction
    (h_flat : ∀ {n m : SimplexCategory} (φ : n ⟶ m),
      ToposHom.IsFlat (ringedToposMap C J (Sheaf.ringSheafOfComm O) φ))
    (n : SimplexCategory) :
    moduleLowerShriekDerived C J O h_flat n ⊣
      (moduleInverseImage C J (Sheaf.ringSheafOfComm O) n).mapDerivedCategory :=
  -- Local instance justification (proof-local temporary data): exactness of `g_{n!}` depends on
  -- `h_flat`.
  letI := moduleLowerShriek_preservesFiniteLimits C J O h_flat n
  letI := moduleLowerShriek_preservesFiniteColimits C J O h_flat n
  Adjunction.mapDerivedCategory
    (stageModuleLowerShriekAdjunction C J O n)

/-- For the pinned `O`-tensor, the monoidal unit on `O_n`-modules is the structure sheaf. -/
def moduleUnitIsoTensorUnit (n : SimplexCategory) :
    SheafOfModules.RingedSite.unitModule ((J n).toGrothendieck)
      ((component C J CommRingCat.{w} n).obj O) ≅
      𝟙_ (SheafOfModules.{w} (componentRingSheaf C J (Sheaf.ringSheafOfComm O) n)) :=
  SheafOfModules.RingedSite.unitIsoTensorUnit

/-- The sheaf-level comparison `g_{n!} F_n ⟶ g_{n!} O_n ⊗ F`. -/
def moduleShriekTensorHom
    (n : SimplexCategory)
    (F : SheafOfModules.{w} (Sheaf.ringSheafOfComm O)) :
    (stageModuleLowerShriek C J O n).obj
        ((moduleInverseImage C J (Sheaf.ringSheafOfComm O) n).obj F) ⟶
      (stageModuleLowerShriek C J O n).obj
          (SheafOfModules.RingedSite.unitModule ((J n).toGrothendieck) ((component C J CommRingCat.{w} n).obj O)) ⊗ F :=
  (stageModuleLowerShriek C J O n).map
      ((MonoidalCategory.leftUnitor
          ((moduleInverseImage C J (Sheaf.ringSheafOfComm O) n).obj F)).inv ≫
        ((moduleUnitIsoTensorUnit C J O n).inv ⊗ₘ
          𝟙 ((moduleInverseImage C J (Sheaf.ringSheafOfComm O) n).obj F))) ≫
    (stageModuleLowerShriekAdjunction C J O n).projectionFormulaMapOf
      (fun X Y ↦ Functor.OplaxMonoidal.δ
        (stageModuleLowerShriek C J O n) X Y)
      (SheafOfModules.RingedSite.unitModule ((J n).toGrothendieck) ((component C J CommRingCat.{w} n).obj O)) F

/-- The sheaf-level adjunct of `moduleShriekTensorHom`, as the left-unitor composite of
the adjunction unit at `O_n` tensored with `F_n`, followed by the strong-monoidal comparison
of `g_n^*`. -/
def moduleShriekTensorMate
    (n : SimplexCategory)
    (F : SheafOfModules.{w} (Sheaf.ringSheafOfComm O)) :
    (moduleInverseImage C J (Sheaf.ringSheafOfComm O) n).obj F ⟶
      (moduleInverseImage C J (Sheaf.ringSheafOfComm O) n).obj
        ((stageModuleLowerShriek C J O n).obj
            (SheafOfModules.RingedSite.unitModule ((J n).toGrothendieck) ((component C J CommRingCat.{w} n).obj O)) ⊗ F) :=
  (MonoidalCategory.leftUnitor
      ((moduleInverseImage C J (Sheaf.ringSheafOfComm O) n).obj F)).inv ≫
    ((moduleUnitIsoTensorUnit C J O n).inv ⊗ₘ
      𝟙 ((moduleInverseImage C J (Sheaf.ringSheafOfComm O) n).obj F)) ≫
    ((stageModuleLowerShriekAdjunction C J O n).unit.app
        (SheafOfModules.RingedSite.unitModule ((J n).toGrothendieck) ((component C J CommRingCat.{w} n).obj O)) ⊗ₘ
      𝟙 ((moduleInverseImage C J (Sheaf.ringSheafOfComm O) n).obj F)) ≫
    LaxMonoidal.μ (moduleInverseImage C J (Sheaf.ringSheafOfComm O) n)
      ((stageModuleLowerShriek C J O n).obj
        (SheafOfModules.RingedSite.unitModule ((J n).toGrothendieck) ((component C J CommRingCat.{w} n).obj O))) F

/-- `moduleShriekTensorHom` is the adjunct of the independent unit-tensor-μ mate. -/
theorem moduleShriekTensorHom_spec
    (n : SimplexCategory)
    (F : SheafOfModules.{w} (Sheaf.ringSheafOfComm O)) :
    moduleShriekTensorHom C J O n F =
      ((stageModuleLowerShriekAdjunction C J O n).homEquiv
          ((moduleInverseImage C J (Sheaf.ringSheafOfComm O) n).obj F)
          ((stageModuleLowerShriek C J O n).obj
              (SheafOfModules.RingedSite.unitModule ((J n).toGrothendieck) ((component C J CommRingCat.{w} n).obj O)) ⊗ F)).symm
        (moduleShriekTensorMate C J O n F) :=
  sorry

/-- The natural transformation whose components are `moduleShriekTensorMate`. -/
def moduleShriekTensorMateNatTrans
    (n : SimplexCategory) :
    moduleInverseImage C J (Sheaf.ringSheafOfComm O) n ⟶
      tensorLeft
          ((stageModuleLowerShriek C J O n).obj
            (SheafOfModules.RingedSite.unitModule ((J n).toGrothendieck) ((component C J CommRingCat.{w} n).obj O))) ⋙
        moduleInverseImage C J (Sheaf.ringSheafOfComm O) n where
  app F := moduleShriekTensorMate C J O n F
  naturality := sorry

/-- The natural transformation whose components are `moduleShriekTensorHom`. -/
def moduleShriekTensorNatTrans
    (n : SimplexCategory) :
    moduleInverseImage C J (Sheaf.ringSheafOfComm O) n ⋙
        stageModuleLowerShriek C J O n ⟶
      tensorLeft
        ((stageModuleLowerShriek C J O n).obj
          (SheafOfModules.RingedSite.unitModule ((J n).toGrothendieck) ((component C J CommRingCat.{w} n).obj O))) where
  app F := moduleShriekTensorHom C J O n F
  naturality := sorry

/-- Tensoring over `O` with `g_{n!} O_n` is additive. -/
instance moduleShriekUnit_tensorLeft_additive (n : SimplexCategory) :
    (tensorLeft
      ((stageModuleLowerShriek C J O n).obj
        (SheafOfModules.RingedSite.unitModule ((J n).toGrothendieck) ((component C J CommRingCat.{w} n).obj O)))).Additive :=
  inferInstance

/-- Tensoring over `O` with `g_{n!} O_n` preserves finite colimits. -/
theorem moduleShriekUnit_tensorLeft_preservesFiniteColimits
    (h_flat : ∀ {n m : SimplexCategory} (φ : n ⟶ m),
      ToposHom.IsFlat (ringedToposMap C J (Sheaf.ringSheafOfComm O) φ))
    (n : SimplexCategory) :
    PreservesFiniteColimits
      (tensorLeft
        ((stageModuleLowerShriek C J O n).obj
          (SheafOfModules.RingedSite.unitModule ((J n).toGrothendieck) ((component C J CommRingCat.{w} n).obj O)))) :=
  sorry

/-- Tensoring over `O` with `g_{n!} O_n` preserves finite limits after the source
flatness hypothesis. -/
theorem moduleShriekUnit_tensorLeft_preservesFiniteLimits
    (h_flat : ∀ {n m : SimplexCategory} (φ : n ⟶ m),
      ToposHom.IsFlat (ringedToposMap C J (Sheaf.ringSheafOfComm O) φ))
    (n : SimplexCategory) :
    PreservesFiniteLimits
      (tensorLeft
        ((stageModuleLowerShriek C J O n).obj
          (SheafOfModules.RingedSite.unitModule ((J n).toGrothendieck) ((component C J CommRingCat.{w} n).obj O)))) :=
  sorry

/-- Derived tensoring on the left by `g_{n!} O_n`. -/
def moduleShriekUnitTensorDerived
    (h_flat : ∀ {n m : SimplexCategory} (φ : n ⟶ m),
      ToposHom.IsFlat (ringedToposMap C J (Sheaf.ringSheafOfComm O) φ))
    (n : SimplexCategory) :
    Hom.ModuleDerived.{w} (totalRingedSite C J (Sheaf.ringSheafOfComm O)) ⥤
      Hom.ModuleDerived.{w} (totalRingedSite C J (Sheaf.ringSheafOfComm O)) :=
  -- Local instance justification (proof-local temporary data): exactness of tensoring with
  -- `g_{n!} O_n` uses the source flatness hypothesis `h_flat`.
  letI := moduleShriekUnit_tensorLeft_preservesFiniteLimits C J O h_flat n
  letI := moduleShriekUnit_tensorLeft_preservesFiniteColimits C J O h_flat n
  (tensorLeft
    ((stageModuleLowerShriek C J O n).obj
      (SheafOfModules.RingedSite.unitModule ((J n).toGrothendieck) ((component C J CommRingCat.{w} n).obj O)))).mapDerivedCategory

/-- The localization-lift of `moduleShriekTensorNatTrans`. -/
def moduleDerivedShriekTensorComparisonComposite
    (h_flat : ∀ {n m : SimplexCategory} (φ : n ⟶ m),
      ToposHom.IsFlat (ringedToposMap C J (Sheaf.ringSheafOfComm O) φ))
    (n : SimplexCategory)
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J (Sheaf.ringSheafOfComm O))) :
    (moduleLowerShriekDerived C J O h_flat n).obj
        ((moduleInverseImage C J (Sheaf.ringSheafOfComm O) n).mapDerivedCategory.obj K) ⟶
      (moduleShriekUnitTensorDerived C J O h_flat n).obj K :=
  -- Local instance justification (proof-local temporary data): exactness of `g_{n!}` and of
  -- tensoring with `g_{n!} O_n` depends on `h_flat`.
  letI := moduleInverseImage_preservesFiniteLimits C J O n
  letI := moduleInverseImage_preservesFiniteColimits C J O n
  letI := moduleLowerShriek_preservesFiniteLimits C J O h_flat n
  letI := moduleLowerShriek_preservesFiniteColimits C J O h_flat n
  letI := moduleShriekUnit_tensorLeft_preservesFiniteLimits C J O h_flat n
  letI := moduleShriekUnit_tensorLeft_preservesFiniteColimits C J O h_flat n
  (ExactFunctor.MapDerivedCategory.compFunctorIso
      (ExactFunctor.of (moduleInverseImage C J (Sheaf.ringSheafOfComm O) n))
      (ExactFunctor.of (stageModuleLowerShriek C J O n))).inv.app K ≫
    (Localization.liftNatTrans DerivedCategory.Q
        (HomologicalComplex.quasiIso _ (up ℤ))
        ((moduleInverseImage C J (Sheaf.ringSheafOfComm O) n ⋙
            stageModuleLowerShriek C J O n).mapHomologicalComplex
          (up ℤ) ⋙ DerivedCategory.Q)
        ((tensorLeft
            ((stageModuleLowerShriek C J O n).obj
              (SheafOfModules.RingedSite.unitModule ((J n).toGrothendieck) ((component C J CommRingCat.{w} n).obj O)))).mapHomologicalComplex
          (up ℤ) ⋙ DerivedCategory.Q)
        (moduleInverseImage C J (Sheaf.ringSheafOfComm O) n ⋙
          stageModuleLowerShriek C J O n).mapDerivedCategory
        (tensorLeft
          ((stageModuleLowerShriek C J O n).obj
            (SheafOfModules.RingedSite.unitModule ((J n).toGrothendieck) ((component C J CommRingCat.{w} n).obj O)))).mapDerivedCategory
        (whiskerRight
          (NatTrans.mapHomologicalComplex (moduleShriekTensorNatTrans C J O n) (up ℤ))
          DerivedCategory.Q)).app K

/-- The canonical comparison `g_{n!} K_n ⟶ g_{n!} O_n ⊗ K`, as the derived functor of exact
tensoring with `g_{n!} O_n`. -/
def moduleDerivedShriekTensorComparison
    (h_flat : ∀ {n m : SimplexCategory} (φ : n ⟶ m),
      ToposHom.IsFlat (ringedToposMap C J (Sheaf.ringSheafOfComm O) φ))
    (n : SimplexCategory)
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J (Sheaf.ringSheafOfComm O))) :
    (moduleLowerShriekDerived C J O h_flat n).obj
        ((moduleInverseImage C J (Sheaf.ringSheafOfComm O) n).mapDerivedCategory.obj K) ⟶
      (moduleShriekUnitTensorDerived C J O h_flat n).obj K :=
  moduleDerivedShriekTensorComparisonComposite C J O h_flat n K

/-- The derived adjunct of `moduleDerivedShriekTensorComparison`, as the left-unitor composite
of the adjunction unit at `O_n` tensored with `K_n`, followed by the strong-monoidal comparison
of `g_n^*`. -/
def moduleDerivedShriekTensorMate
    (h_flat : ∀ {n m : SimplexCategory} (φ : n ⟶ m),
      ToposHom.IsFlat (ringedToposMap C J (Sheaf.ringSheafOfComm O) φ))
    (n : SimplexCategory)
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J (Sheaf.ringSheafOfComm O))) :
    (moduleInverseImage C J (Sheaf.ringSheafOfComm O) n).mapDerivedCategory.obj K ⟶
      (moduleInverseImage C J (Sheaf.ringSheafOfComm O) n).mapDerivedCategory.obj
        ((moduleShriekUnitTensorDerived C J O h_flat n).obj K) :=
  -- Local instance justification (proof-local temporary data): exactness of tensoring with
  -- `g_{n!} O_n` depends on `h_flat`.
  letI := moduleShriekUnit_tensorLeft_preservesFiniteLimits C J O h_flat n
  letI := moduleShriekUnit_tensorLeft_preservesFiniteColimits C J O h_flat n
  (Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (up ℤ))
      ((moduleInverseImage C J (Sheaf.ringSheafOfComm O) n).mapHomologicalComplex
        (up ℤ) ⋙ DerivedCategory.Q)
      ((tensorLeft
            ((stageModuleLowerShriek C J O n).obj
              (SheafOfModules.RingedSite.unitModule ((J n).toGrothendieck) ((component C J CommRingCat.{w} n).obj O))) ⋙
          moduleInverseImage C J (Sheaf.ringSheafOfComm O) n).mapHomologicalComplex
        (up ℤ) ⋙ DerivedCategory.Q)
      (moduleInverseImage C J (Sheaf.ringSheafOfComm O) n).mapDerivedCategory
      (tensorLeft
          ((stageModuleLowerShriek C J O n).obj
            (SheafOfModules.RingedSite.unitModule ((J n).toGrothendieck) ((component C J CommRingCat.{w} n).obj O))) ⋙
        moduleInverseImage C J (Sheaf.ringSheafOfComm O) n).mapDerivedCategory
      (whiskerRight
        (NatTrans.mapHomologicalComplex (moduleShriekTensorMateNatTrans C J O n) (up ℤ))
        DerivedCategory.Q)).app K ≫
    (ExactFunctor.MapDerivedCategory.compFunctorIso
        (ExactFunctor.of
          (tensorLeft
            ((stageModuleLowerShriek C J O n).obj
              (SheafOfModules.RingedSite.unitModule ((J n).toGrothendieck) ((component C J CommRingCat.{w} n).obj O)))))
        (ExactFunctor.of (moduleInverseImage C J (Sheaf.ringSheafOfComm O) n))).hom.app K

/-- `moduleDerivedShriekTensorComparison` is the derived adjunct of the left-unitor composite
of the adjunction unit at `O_n` tensored with `K_n`. -/
theorem moduleDerivedShriekTensorComparison_spec
    (h_flat : ∀ {n m : SimplexCategory} (φ : n ⟶ m),
      ToposHom.IsFlat (ringedToposMap C J (Sheaf.ringSheafOfComm O) φ))
    (n : SimplexCategory)
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J (Sheaf.ringSheafOfComm O))) :
    moduleDerivedShriekTensorComparison C J O h_flat n K =
      ((moduleDerivedLowerShriekAdjunction C J O h_flat n).homEquiv
          ((moduleInverseImage C J (Sheaf.ringSheafOfComm O) n).mapDerivedCategory.obj K)
          ((moduleShriekUnitTensorDerived C J O h_flat n).obj K)).symm
        (moduleDerivedShriekTensorMate C J O h_flat n K) :=
  sorry

end Modules

end CategoryTheory.SimplicialSites
