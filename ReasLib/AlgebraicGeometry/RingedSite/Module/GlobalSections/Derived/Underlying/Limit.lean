/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Underlying
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sequential derived limits of objectwise sections

This leaf owns the sequential-limit API for module-valued sections and their underlying additive
model without adding derived-limit dependencies to the basic comparison file.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe z u v w

namespace RingedSite.Hom.ModuleSections

variable (X : RingedSite.{u, v, w})

namespace Underlying

/-- The degree-`q` cohomology tower obtained by applying underlying additive derived sections over
`U` to a sequential inverse system of derived modules. -/
@[stacks 0D6K "underlying additive objectwise cohomology tower"]
abbrev cohomologyTower (U : X)
    [UnivLE.{max u v, z}]
    [Functor.HasRightDerivedFunctor
      (sectionsToDerived X U) (ModuleQis.{z} X)]
    (Ksys : SequentialInverseSystem (ModuleDerived.{z} X)) (q : ℤ) :
    SequentialInverseSystem AddCommGrpCat.{z} :=
  Ksys ⋙ Functor.totalRightDerived (sectionsToDerived.{z} X U)
    (moduleLocalization.{z} X) (ModuleQis.{z} X) ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{z} q

/-- Underlying additive derived sections over an object preserve sequential derived limits. -/
@[stacks 0D6K "underlying additive sections preserve sequential derived limits"]
theorem sectionsDerived_preservesDerivedLimit
    [UnivLE.{max u v, z}]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{z} X)] (U : X)
    {Ksys : SequentialInverseSystem (ModuleDerived.{z} X)}
    {K : ModuleDerived.{z} X} (hK : IsDerivedLimit Ksys K) :
    Nonempty
      (IsDerivedLimit (Ksys ⋙ sectionsDerived X U)
        ((sectionsDerived X U).obj K)) := sorry

end Underlying

/-- Module-valued derived sections over an object preserve sequential derived limits. -/
@[stacks 0D6K "module-valued sections preserve sequential derived limits"]
theorem sectionsDerived_preservesDerivedLimit
    [UnivLE.{max u v, z}]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{z} X)] (U : X)
    {Ksys : SequentialInverseSystem (ModuleDerived.{z} X)}
    {K : ModuleDerived.{z} X} (hK : IsDerivedLimit Ksys K) :
    Nonempty
      (IsDerivedLimit (Ksys ⋙ moduleSectionsDerived.{z} X U)
        ((moduleSectionsDerived.{z} X U).obj K)) := sorry

end RingedSite.Hom.ModuleSections
