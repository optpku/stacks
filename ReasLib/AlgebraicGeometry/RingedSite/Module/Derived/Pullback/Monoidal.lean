/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.KFlat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.KFlat.Monoidal
public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.TermwiseFlat.QuasiIso
import Mathlib.Tactic.CrossRefAttribute

/-!
# Monoidal derived pullback from good flat models

The canonical comparison on K-flat complexes with flat terms identifies total derived pullback
with ordinary pullback followed by localization. Its invertibility is kept separate from the
comparison data. Only a caller-supplied `IsIso` instance is used to construct localization lifting
and strong monoidal data.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom.modulePullbackDerived

variable {C : Type uX} [Category.{vX} C] {D : Type uY} [Category.{vY} D]
variable {JX : GrothendieckTopology C} {JY : GrothendieckTopology D}
variable [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}
variable [HasWeakSheafify JX AddCommGrpCat.{w}]
variable [JX.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JY AddCommGrpCat.{w}]
variable [JY.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]

variable (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JX OX)
  (RingedSite.ofCommRingSheaf JY OY))
variable [(f.modulePushforward.{w}).IsRightAdjoint]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{w} f)
  (ModuleQis.{w} (RingedSite.ofCommRingSheaf JY OY))]

namespace GoodModels

/-- The source localization in the good-model comparison, reassociated through the direct
homotopy-category inclusion. -/
noncomputable def sourceIso :
    ModuleDerived.KFlat.TermwiseFlat.localizationFunctor OY ⋙
        modulePullbackDerived.{w} f ≅
      (HomotopyCategory.KFlat.termwiseFlat
          (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY))).ι ⋙
        (moduleLocalization.{w} (RingedSite.ofCommRingSheaf JY OY) ⋙
          modulePullbackDerived.{w} f) :=
  Functor.isoWhiskerRight
      (ModuleDerived.KFlat.TermwiseFlat.localizationFunctorIso OY)
      (modulePullbackDerived.{w} f) ≪≫
    Functor.associator _ _ _

/-- The target localization in the good-model comparison, reassociated through restricted
homotopy pullback. -/
noncomputable def targetIso :
    modulePullbackHomotopy.goodModels f ⋙
        ModuleDerived.KFlat.TermwiseFlat.localizationFunctor OX ≅
      (HomotopyCategory.KFlat.termwiseFlat
          (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY))).ι ⋙
        (modulePullbackHomotopy f ⋙
          moduleLocalization.{w} (RingedSite.ofCommRingSheaf JX OX)) :=
  Functor.isoWhiskerLeft (modulePullbackHomotopy.goodModels f)
      (ModuleDerived.KFlat.TermwiseFlat.localizationFunctorIso OX) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (modulePullbackHomotopy.goodModels.compιIso f)
      (moduleLocalization.{w} (RingedSite.ofCommRingSheaf JX OX)) ≪≫
    Functor.associator _ _ _

/-- The canonical comparison from derived pullback of localized good models to ordinary
good-model pullback followed by localization. -/
@[stacks 07A4 "derived pullback good-model comparison"]
noncomputable def comparison :
    ModuleDerived.KFlat.TermwiseFlat.localizationFunctor OY ⋙
        modulePullbackDerived.{w} f ⟶
      modulePullbackHomotopy.goodModels f ⋙
        ModuleDerived.KFlat.TermwiseFlat.localizationFunctor OX :=
  (sourceIso f).hom ≫
    Functor.whiskerLeft
      (HomotopyCategory.KFlat.termwiseFlat
        (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY))).ι
      ((modulePullbackToDerived.{w} f).totalLeftDerivedCounit
        (moduleLocalization.{w} (RingedSite.ofCommRingSheaf JY OY))
        (ModuleQis.{w} (RingedSite.ofCommRingSheaf JY OY))) ≫
    (targetIso f).inv

/-- The good-model comparison for derived module pullback is invertible. It remains a theorem,
not an instance, so its deferred proof cannot choose inverse data. -/
@[stacks 07A4 "derived pullback good-model comparison is invertible"]
theorem comparison_isIso : IsIso (comparison f) := sorry

variable [IsIso (comparison f)]

/-- The good-model comparison as an isomorphism, conditional on caller-supplied invertibility. -/
@[stacks 07A4 "derived pullback good-model comparison isomorphism"]
noncomputable abbrev comparisonIso :
    ModuleDerived.KFlat.TermwiseFlat.localizationFunctor OY ⋙
        modulePullbackDerived.{w} f ≅
      modulePullbackHomotopy.goodModels f ⋙
        ModuleDerived.KFlat.TermwiseFlat.localizationFunctor OX :=
  asIso (comparison f)

/-- The canonical localization lifting of derived pullback through good flat models. -/
@[stacks 07A4 "derived pullback good-model lifting", implicit_reducible]
noncomputable instance lifting :
    Localization.Lifting
      (ModuleDerived.KFlat.TermwiseFlat.localizationFunctor OY)
      (HomotopyCategory.KFlat.TermwiseFlat.quasiIso
        (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)))
      (modulePullbackHomotopy.goodModels f ⋙
        ModuleDerived.KFlat.TermwiseFlat.localizationFunctor OX)
      (modulePullbackDerived.{w} f) where
  iso := comparisonIso f

end GoodModels

variable [Functor.Monoidal f.modulePullback.{w}]
variable [ModuleDerived.KFlat.HomotopyTensorDescends (J := JX) OX]
variable [ModuleDerived.KFlat.HomotopyTensorDescends (J := JY) OY]
variable [ModuleDerived.KFlat.TensorDescends (J := JX) OX]
variable [ModuleDerived.KFlat.TensorDescends (J := JY) OY]
variable [ModuleDerived.KFlat.IsLocalization (J := JX) OX]
variable [ModuleDerived.KFlat.IsLocalization (J := JY) OY]
variable [ModuleDerived.KFlat.TermwiseFlat.IsLocalization (J := JY) OY]
variable [Functor.Homotopy.Cochain.TensorComparison.IsInvertible f.modulePullback.{w}]
variable [IsIso (GoodModels.comparison f)]

-- Local instance justification (defeq pin): use the canonical restricted pullback
-- monoidal structure, which is deliberately exposed as a named definition.
attribute [local instance] modulePullbackHomotopy.goodModels.monoidal

/-- The strong monoidal core on derived module pullback obtained by descent from good flat
models. -/
@[stacks 07A4 "derived pullback monoidal core"]
noncomputable def coreMonoidal : (modulePullbackDerived.{w} f).CoreMonoidal :=
  Localization.Monoidal.functorCoreMonoidalOfComp
    (ModuleDerived.KFlat.TermwiseFlat.localizationFunctor OY)
    (HomotopyCategory.KFlat.TermwiseFlat.quasiIso
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)))
    (modulePullbackDerived.{w} f)
    (modulePullbackHomotopy.goodModels f ⋙
      ModuleDerived.KFlat.TermwiseFlat.localizationFunctor OX)

/-- Derived module pullback is strong monoidal once the canonical good-model comparison and
localization boundaries are supplied. -/
@[stacks 07A4 "derived pullback monoidal functor", implicit_reducible]
noncomputable instance monoidal : (modulePullbackDerived.{w} f).Monoidal :=
  (coreMonoidal f).toMonoidal

/-- The unit isomorphism of the strong monoidal derived pullback functor. -/
noncomputable abbrev mapUnitIso :
    𝟙_ (ModuleDerived.{w} (RingedSite.ofCommRingSheaf JX OX)) ≅
      (modulePullbackDerived.{w} f).obj
        (𝟙_ (ModuleDerived.{w} (RingedSite.ofCommRingSheaf JY OY))) :=
  Functor.Monoidal.εIso (modulePullbackDerived.{w} f)

/-- The bifunctorial tensorator of the strong monoidal derived pullback functor. -/
@[stacks 07A4 "derived pullback tensorator"]
noncomputable abbrev mapTensorNatIso :
    Functor.prod (modulePullbackDerived.{w} f)
          (modulePullbackDerived.{w} f) ⋙
        MonoidalCategory.tensor
          (ModuleDerived.{w} (RingedSite.ofCommRingSheaf JX OX)) ≅
      MonoidalCategory.tensor
          (ModuleDerived.{w} (RingedSite.ofCommRingSheaf JY OY)) ⋙
        modulePullbackDerived.{w} f :=
  Functor.Monoidal.μNatIso (modulePullbackDerived.{w} f)

/-- The tensorator of the strong monoidal derived pullback functor. -/
noncomputable abbrev mapTensorIso
    (K L : ModuleDerived.{w} (RingedSite.ofCommRingSheaf JY OY)) :
    (modulePullbackDerived.{w} f).obj K ⊗
        (modulePullbackDerived.{w} f).obj L ≅
      (modulePullbackDerived.{w} f).obj (K ⊗ L) :=
  (mapTensorNatIso f).app (K, L)

namespace TensorPreservation

/-- Lemma 21.18.4 (07A4): the bifunctorial isomorphism from derived pullback of a derived
tensor product to the derived tensor product of the pullbacks. -/
@[stacks 07A4 "derived pullback preserves tensor products"]
noncomputable abbrev natIso :
    MonoidalCategory.tensor
          (ModuleDerived.{w} (RingedSite.ofCommRingSheaf JY OY)) ⋙
        modulePullbackDerived.{w} f ≅
      Functor.prod (modulePullbackDerived.{w} f)
          (modulePullbackDerived.{w} f) ⋙
        MonoidalCategory.tensor
          (ModuleDerived.{w} (RingedSite.ofCommRingSheaf JX OX)) :=
  (mapTensorNatIso f).symm

/-- The component of the derived pullback tensor comparison at two objects. -/
@[stacks 07A4 "pointwise derived pullback tensor comparison"]
noncomputable abbrev iso
    (K L : ModuleDerived.{w} (RingedSite.ofCommRingSheaf JY OY)) :
    (modulePullbackDerived.{w} f).obj (K ⊗ L) ≅
      (modulePullbackDerived.{w} f).obj K ⊗
        (modulePullbackDerived.{w} f).obj L :=
  (natIso f).app (K, L)

/-- The canonical source-facing morphism underlying derived pullback's tensor comparison. -/
@[stacks 07A4 "tensor comparison morphism"]
noncomputable abbrev hom
    (K L : ModuleDerived.{w} (RingedSite.ofCommRingSheaf JY OY)) :
    (modulePullbackDerived.{w} f).obj (K ⊗ L) ⟶
      (modulePullbackDerived.{w} f).obj K ⊗
        (modulePullbackDerived.{w} f).obj L :=
  (iso f K L).hom

end TensorPreservation

end RingedSite.Hom.modulePullbackDerived
