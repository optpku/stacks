# ReasLib modules referenced by the UML statement and interfaces

These lists come from elaborated Lean declarations on the pinned Lean 4.32.0 / Mathlib toolchain. They retain declaration types and non-`Prop` definition bodies, skip the bodies of proposition-valued declarations, and expand constructors of reached ReasLib structures/inductives to retain field specifications. Inline proof references inside retained data definitions remain in the trace. Generated declarations are included.

Each row names the owner of a referenced declaration. Building an owner module still loads its own imports. The lists describe the current statement/data representation; they do not assert a minimum across equivalent mathematical presentations or form an isolated build allowlist.

The [machine-readable report](validation/required-reaslib-dependencies.json) lists every declaration witness. The [compile experiments](validation/import-necessity-experiments.json) separately identify tested import entry points.

## Theorem 1.1 statement and data dependencies

**49 modules, 274 declarations**, rooted only at `UniformMordellLang.theorem_1_1`.

| Owner module | Referenced declarations | Example witness |
|---|---:|---|
| [ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Additive](jacobian-foundations/ReasLib/Algebra/Category/ModuleCat/ChangeOfRings/Additive.lean) | 1 | `ModuleCat.ExtendScalars.additive` |
| [ReasLib.Algebra.Category.ModuleCat.Presheaf.CommRing](jacobian-foundations/ReasLib/Algebra/Category/ModuleCat/Presheaf/CommRing.lean) | 2 | `PresheafOfModules.presheafStructureMap` |
| [ReasLib.Algebra.Category.ModuleCat.Presheaf.Pullback.Monoidal](jacobian-foundations/ReasLib/Algebra/Category/ModuleCat/Presheaf/Pullback/Monoidal.lean) | 5 | `PresheafOfModules.Pullback.pullbackCoreMonoidalOf` |
| [ReasLib.Algebra.Category.ModuleCat.Presheaf.Stalk](jacobian-foundations/ReasLib/Algebra/Category/ModuleCat/Presheaf/Stalk.lean) | 8 | `PresheafOfModules.stalkFunctorOfCommRing` |
| [ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Pushforward](jacobian-foundations/ReasLib/Algebra/Category/ModuleCat/Presheaf/Tensor/Pushforward.lean) | 26 | `PresheafOfModules.Pushforward.laxMonoidal` |
| [ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Restriction](jacobian-foundations/ReasLib/Algebra/Category/ModuleCat/Presheaf/Tensor/Restriction.lean) | 12 | `PresheafOfModules.Restriction.functor` |
| [ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed](jacobian-foundations/ReasLib/Algebra/Category/ModuleCat/Sheaf/Monoidal/Ringed.lean) | 50 | `SheafOfModules.RingedSite.Tensor.monoidalCategory` |
| [ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite](jacobian-foundations/ReasLib/Algebra/Category/ModuleCat/Sheaf/RingedSite.lean) | 2 | `SheafOfModules.RingedSite.ringSheaf` |
| [ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PresheafMonoidal](jacobian-foundations/ReasLib/Algebra/Category/ModuleCat/Sheaf/RingedSite/PresheafMonoidal.lean) | 3 | `SheafOfModules.RingedSite.Tensor.Presheaf.monoidalCategory` |
| [ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Pullback.Monoidal](jacobian-foundations/ReasLib/Algebra/Category/ModuleCat/Sheaf/RingedSite/Pullback/Monoidal.lean) | 15 | `SheafOfModules.Pullback.Construction.compositeMonoidalOf` |
| [ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk](jacobian-foundations/ReasLib/Algebra/Category/ModuleCat/Sheaf/Stalk.lean) | 1 | `SheafOfModules.stalkFunctorOfCommRing` |
| [ReasLib.Algebra.Category.Ring.Sheaf](jacobian-foundations/ReasLib/Algebra/Category/Ring/Sheaf.lean) | 4 | `CategoryTheory.Presheaf.ringPresheafOfComm` |
| [ReasLib.Algebra.Homology.DerivedCategory.ModuleCat](jacobian-foundations/ReasLib/Algebra/Homology/DerivedCategory/ModuleCat.lean) | 1 | `ModuleCat.hasDerivedCategory` |
| [ReasLib.Algebra.Homology.DerivedCategory.ResidueField.MinimalFreeModel](jacobian-foundations/ReasLib/Algebra/Homology/DerivedCategory/ResidueField/MinimalFreeModel.lean) | 4 | `CategoryTheory.DerivedCategory.ResidueField.homology` |
| [ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension](jacobian-foundations/ReasLib/Algebra/Homology/DerivedCategory/ScalarExtension.lean) | 5 | `CategoryTheory.ModuleCat.derivedExtensionOfScalars` |
| [ReasLib.AlgebraicGeometry.RingedSite.Module.Basic](jacobian-foundations/ReasLib/AlgebraicGeometry/RingedSite/Module/Basic.lean) | 4 | `RingedSite.CommRingPresentation.moduleAbelian` |
| [ReasLib.AlgebraicGeometry.RingedSpace.Definition](jacobian-foundations/ReasLib/AlgebraicGeometry/RingedSpace/Definition.lean) | 4 | `AlgebraicGeometry.RingedSpace.Hom.commRingSheafPushforwardMap` |
| [ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition](jacobian-foundations/ReasLib/AlgebraicGeometry/RingedSpace/Module/Definition.lean) | 6 | `AlgebraicGeometry.RingedSpace.Hom.pullback` |
| [ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic](jacobian-foundations/ReasLib/AlgebraicGeometry/RingedSpace/Module/Derived/Basic.lean) | 5 | `AlgebraicGeometry.RingedSpace.ModuleDerived` |
| [ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward](jacobian-foundations/ReasLib/AlgebraicGeometry/RingedSpace/Module/Derived/Pushforward.lean) | 3 | `AlgebraicGeometry.RingedSpace.moduleDerivedPushforward` |
| [ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections](jacobian-foundations/ReasLib/AlgebraicGeometry/RingedSpace/Module/Derived/Sections.lean) | 4 | `AlgebraicGeometry.RingedSpace.moduleCohomologyAtOpenFunctor` |
| [ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Stalk](jacobian-foundations/ReasLib/AlgebraicGeometry/RingedSpace/Module/Derived/TorDimension/Stalk.lean) | 6 | `AlgebraicGeometry.RingedSpace.ModuleDerived.Stalk.functor` |
| [ReasLib.AlgebraicGeometry.RingedSpace.Module.Monoidal](jacobian-foundations/ReasLib/AlgebraicGeometry/RingedSpace/Module/Monoidal.lean) | 5 | `AlgebraicGeometry.RingedSpace.modulesMonoidalCategory` |
| [ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Monoidal](jacobian-foundations/ReasLib/AlgebraicGeometry/RingedSpace/Module/Pullback/Monoidal.lean) | 7 | `AlgebraicGeometry.RingedSpace.Hom.pullbackCoreMonoidal` |
| [ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Basic](jacobian-foundations/ReasLib/AlgebraicGeometry/RingedSpace/Module/Sections/Basic.lean) | 3 | `AlgebraicGeometry.RingedSpace.moduleSectionsEvaluationFunctor` |
| [ReasLib.AlgebraicGeometry.Scheme.GlobalSections](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/GlobalSections.lean) | 2 | `AlgebraicGeometry.Scheme.Hom.globalSectionsMap` |
| [ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Module/Cohomology.lean) | 2 | `AlgebraicGeometry.Scheme.Modules.cohomologyFunctor` |
| [ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Module/Cohomology/GlobalSections.lean) | 3 | `AlgebraicGeometry.Scheme.Hom.cohomology` |
| [ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Module/Derived/Basic.lean) | 1 | `AlgebraicGeometry.Scheme.Modules.schemeModulesHasDerivedCategory` |
| [ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FiberEulerCharacteristic](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Module/Derived/FiberEulerCharacteristic.lean) | 3 | `AlgebraicGeometry.Scheme.ModuleDerived.fiberEulerChar` |
| [ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.FiberEulerCharacteristic](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Module/Derived/Pushforward/FiberEulerCharacteristic.lean) | 5 | `AlgebraicGeometry.Scheme.Modules.relativeEulerChar` |
| [ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Module/Monoidal.lean) | 2 | `AlgebraicGeometry.Scheme.Modules.instMonoidalCategory` |
| [ReasLib.AlgebraicGeometry.Scheme.Module.Picard](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Module/Picard.lean) | 2 | `AlgebraicGeometry.Scheme.PicardGroup` |
| [ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Module/Picard/Pullback.lean) | 1 | `AlgebraicGeometry.Scheme.Hom.picardPullback` |
| [ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Module/Picard/Relative.lean) | 5 | `AlgebraicGeometry.RelativePicard.functor` |
| [ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Components](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Module/Picard/Relative/Components.lean) | 2 | `AlgebraicGeometry.RelativePicard.component` |
| [ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Degree](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Module/Picard/Relative/Degree.lean) | 7 | `AlgebraicGeometry.RelativePicard.degreePresheaf` |
| [ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Fppf](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Module/Picard/Relative/Fppf.lean) | 5 | `AlgebraicGeometry.RelativePicard.additiveFppfSheaf` |
| [ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Group](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Module/Picard/Relative/Group.lean) | 11 | `AlgebraicGeometry.RelativePicard.DegreeZeroIsSubgroup` |
| [ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Group.Basic](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Module/Picard/Relative/Group/Basic.lean) | 14 | `AlgebraicGeometry.RelativePicard.functorSheafificationIso` |
| [ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Presheaf](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Module/Picard/Relative/Presheaf.lean) | 5 | `AlgebraicGeometry.RelativePicard.groupPresheaf` |
| [ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Module/Pullback/Monoidal.lean) | 1 | `AlgebraicGeometry.Scheme.Modules.pullbackMonoidal` |
| [ReasLib.AlgebraicGeometry.Scheme.OverSpec](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/OverSpec.lean) | 1 | `AlgebraicGeometry.Scheme.homToSpecGlobalSectionsEquiv` |
| [ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive](jacobian-foundations/ReasLib/CategoryTheory/DerivedCategory/Functor/Induced/Preadditive.lean) | 2 | `CategoryTheory.Functor.Homotopy.toDerived` |
| [ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived](jacobian-foundations/ReasLib/CategoryTheory/DerivedCategory/Functor/TotalLeftDerived.lean) | 2 | `CategoryTheory.Functor.LeftDerived.Homotopy.functor` |
| [ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived](jacobian-foundations/ReasLib/CategoryTheory/DerivedCategory/Functor/TotalRightDerived.lean) | 2 | `CategoryTheory.Functor.RightDerived.KInjective.HasDerived` |
| [ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy](jacobian-foundations/ReasLib/CategoryTheory/DerivedCategory/Functor/TotalRightDerived/Homotopy.lean) | 2 | `CategoryTheory.Functor.RightDerived.Homotopy.functor` |
| [ReasLib.CategoryTheory.Monoidal.Picard](jacobian-foundations/ReasLib/CategoryTheory/Monoidal/Picard.lean) | 5 | `CategoryTheory.MonoidalCategory.PicardGroup` |
| [ReasLib.Topology.Sheaves.Ring.Definition](jacobian-foundations/ReasLib/Topology/Sheaves/Ring/Definition.lean) | 3 | `TopCat.Sheaf.ringSheafOfComm` |

## Additional owners for the six application interfaces

Including genus, Jacobian, group structure, the pointed Abel–Jacobi map, the bound, and the final theorem gives **79 modules, 460 declarations**. The following **30 additional modules** extend the theorem-only owner set. Declaration counts in this table use the six-root traversal. That traversal also reaches additional declarations in some of the first 49 modules; this table lists only the newly reached owner modules.

| Owner module | Referenced declarations | Example witness |
|---|---:|---|
| [ReasLib.Algebra.Category.ModuleCat.Presheaf.Over](jacobian-foundations/ReasLib/Algebra/Category/ModuleCat/Presheaf/Over.lean) | 2 | `PresheafOfModules.over` |
| [ReasLib.Algebra.Category.ModuleCat.Presheaf.OverSections](jacobian-foundations/ReasLib/Algebra/Category/ModuleCat/Presheaf/OverSections.lean) | 2 | `PresheafOfModules.overSectionsEquivEvaluation` |
| [ReasLib.Algebra.Category.ModuleCat.Presheaf.SectionAction](jacobian-foundations/ReasLib/Algebra/Category/ModuleCat/Presheaf/SectionAction.lean) | 5 | `PresheafOfModules.SectionAction.app` |
| [ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Bilinear](jacobian-foundations/ReasLib/Algebra/Category/ModuleCat/Presheaf/Tensor/Bilinear.lean) | 17 | `PresheafOfModules.BilinearMap` |
| [ReasLib.Algebra.Category.ModuleCat.Sheaf.OverSections](jacobian-foundations/ReasLib/Algebra/Category/ModuleCat/Sheaf/OverSections.lean) | 2 | `SheafOfModules.overSectionsEquivEvaluation` |
| [ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom](jacobian-foundations/ReasLib/Algebra/Category/ModuleCat/Sheaf/RingedSite/InternalHom.lean) | 83 | `SheafOfModules.RingedSite.InternalHom.Bilinear.homEquiv` |
| [ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal](jacobian-foundations/ReasLib/Algebra/Category/ModuleCat/Sheaf/RingedSite/KernelIdeal.lean) | 4 | `SheafOfModules.RingedSite.KernelIdeal.map` |
| [ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocalSectionMul](jacobian-foundations/ReasLib/Algebra/Category/ModuleCat/Sheaf/RingedSite/LocalSectionMul.lean) | 6 | `SheafOfModules.sectionAction` |
| [ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Sheafification](jacobian-foundations/ReasLib/Algebra/Category/ModuleCat/Sheaf/RingedSite/Sheafification.lean) | 3 | `moduleSheafification` |
| [ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction](jacobian-foundations/ReasLib/Algebra/Category/ModuleCat/Sheaf/RingedSite/SheafificationAdjunction.lean) | 15 | `SheafOfModules.RingedSite.moduleSheafificationAdjunction` |
| [ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationMonoidal](jacobian-foundations/ReasLib/Algebra/Category/ModuleCat/Sheaf/RingedSite/SheafificationMonoidal.lean) | 1 | `SheafOfModules.RingedSite.ModuleSheafification.tensorObjIso` |
| [ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor](jacobian-foundations/ReasLib/Algebra/Category/ModuleCat/Sheaf/RingedSite/Tensor.lean) | 1 | `SheafOfModules.RingedSite.moduleTensor` |
| [ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Bilinear](jacobian-foundations/ReasLib/Algebra/Category/ModuleCat/Sheaf/RingedSite/Tensor/Bilinear.lean) | 2 | `SheafOfModules.RingedSite.SectionBilinearMap` |
| [ReasLib.AlgebraicGeometry.RingedSpace.IdealSubobject](jacobian-foundations/ReasLib/AlgebraicGeometry/RingedSpace/IdealSubobject.lean) | 1 | `AlgebraicGeometry.RingedSpace.IdealSubobject` |
| [ReasLib.AlgebraicGeometry.RingedSpace.IdealSubobject.Kernel](jacobian-foundations/ReasLib/AlgebraicGeometry/RingedSpace/IdealSubobject/Kernel.lean) | 3 | `AlgebraicGeometry.RingedSpace.Hom.kernelIdealSheaf` |
| [ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedImmersion](jacobian-foundations/ReasLib/AlgebraicGeometry/RingedSpace/Module/ClosedImmersion.lean) | 1 | `AlgebraicGeometry.RingedSpace.Hom.idealSheaf` |
| [ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Divisor/EffectiveCartier.lean) | 2 | `AlgebraicGeometry.IsEffectiveCartierDivisor` |
| [ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.AssociatedSheaf](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Divisor/EffectiveCartier/AssociatedSheaf.lean) | 1 | `AlgebraicGeometry.Scheme.effectiveCartierDivisorAssociatedSheaf` |
| [ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Graph](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Divisor/EffectiveCartier/Graph.lean) | 4 | `AlgebraicGeometry.SchemeOver.graph` |
| [ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Graph.Cartier](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Divisor/EffectiveCartier/Graph/Cartier.lean) | 2 | `AlgebraicGeometry.SchemeOver.graphIdeal_isEffectiveCartier` |
| [ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Divisor/EffectiveCartier/IdealSheaf.lean) | 2 | `AlgebraicGeometry.Scheme.IdealSheafData.associatedSheaf` |
| [ReasLib.AlgebraicGeometry.Scheme.IdealSubobject](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/IdealSubobject.lean) | 3 | `AlgebraicGeometry.Scheme.Hom.kernelIdealSubobject` |
| [ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Module/Invertible/Basic.lean) | 1 | `AlgebraicGeometry.Scheme.Modules.Invertible` |
| [ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Pointed](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Module/Picard/Relative/Pointed.lean) | 2 | `AlgebraicGeometry.RelativePicard.sectionClass` |
| [ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Morphism/FiniteType.lean) | 2 | `AlgebraicGeometry.Scheme.Hom.FiniteType` |
| [ReasLib.AlgebraicGeometry.Scheme.OverField](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/OverField.lean) | 1 | `AlgebraicGeometry.SchemeOverField` |
| [ReasLib.AlgebraicGeometry.Scheme.Variety](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Variety.lean) | 2 | `AlgebraicGeometry.Variety` |
| [ReasLib.AlgebraicGeometry.Scheme.Variety.Curve](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Variety/Curve.lean) | 2 | `AlgebraicGeometry.Curve` |
| [ReasLib.CategoryTheory.Functor.SectionsTerminal](jacobian-foundations/ReasLib/CategoryTheory/Functor/SectionsTerminal.lean) | 2 | `CategoryTheory.Functor.sectionsEquivInitial` |
| [ReasLib.CategoryTheory.Monoidal.Invertible](jacobian-foundations/ReasLib/CategoryTheory/Monoidal/Invertible.lean) | 2 | `CategoryTheory.MonoidalCategory.isInvertibleObject` |

## Reproduce the declaration trace

After the application build, run from this application directory:

```sh
cd annals-uniform-mordell-lang
lake env lean ../analysis/TraceReasLibDependencies.lean
```

The report is written to `.work/reuse/declaration-use.json`. It also records the larger closures obtained when existing proof bodies are included. Those counts are kept separate from statement/data dependencies.
