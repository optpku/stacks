module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat.Coproduct
public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.TermwiseFlat.Monoidal
public import ReasLib.Algebra.Homology.HomotopyCategory.Monoidal.Cochain
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.KFlat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Monoidal
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Monoidal pullback on good flat models

The termwise pullback of complexes has a canonical tensor comparison. After passage to the
homotopy category, its invertibility is the exact proof boundary needed to restrict pullback to a
strong monoidal functor on K-flat complexes with flat terms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom.modulePullbackHomotopy

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
variable [Functor.Monoidal f.modulePullback.{w}]
variable [HomotopyCategory.Koszul.TensorDescends
  (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf JX OX))]
variable [HomotopyCategory.Koszul.TensorDescends
  (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY))]

namespace TensorComparison

/-- The canonical homotopy-level tensor comparison for module pullback is invertible. This is a
theorem rather than an instance because its deferred proof must not select inverse data. -/
@[stacks 07A4 "homotopy pullback tensor comparison"]
theorem isInvertible :
    Functor.Homotopy.Cochain.TensorComparison.IsInvertible f.modulePullback.{w} := sorry

end TensorComparison

namespace goodModels

variable [Functor.Homotopy.Cochain.TensorComparison.IsInvertible f.modulePullback.{w}]

/-- The canonical strong monoidal core on pullback restricted to K-flat homotopy objects with
flat terms. -/
@[stacks 07A4 "monoidal pullback on good flat models"]
noncomputable def coreMonoidal :
    @Functor.CoreMonoidal
      (HomotopyCategory.KFlat.TermwiseFlat
        (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY))) _
      (@ObjectProperty.fullMonoidalSubcategory _ _ _ _
        (CategoryTheory.HomotopyCategory.KFlat.TermwiseFlat.isMonoidal
          (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY))))
      (HomotopyCategory.KFlat.TermwiseFlat
        (ModuleCat.{w} (RingedSite.ofCommRingSheaf JX OX))) _
      (@ObjectProperty.fullMonoidalSubcategory _ _ _ _
        (CategoryTheory.HomotopyCategory.KFlat.TermwiseFlat.isMonoidal
          (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf JX OX))))
      (goodModels f) :=
  @ObjectProperty.FullSubcategory.restrict.coreMonoidal
    (HomotopyCategory (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)) (up ℤ)) _ _
    (HomotopyCategory (ModuleCat.{w} (RingedSite.ofCommRingSheaf JX OX)) (up ℤ)) _ _
    (HomotopyCategory.KFlat.termwiseFlat
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)))
    (HomotopyCategory.KFlat.termwiseFlat
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JX OX)))
    (CategoryTheory.HomotopyCategory.KFlat.TermwiseFlat.isMonoidal
      (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)))
    (CategoryTheory.HomotopyCategory.KFlat.TermwiseFlat.isMonoidal
      (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf JX OX)))
    (modulePullbackHomotopy f) _ (fun _ hK ↦ termwiseFlat f hK)

/-- Pullback on good flat models is strong monoidal, conditional exactly on invertibility of its
canonical homotopy-level tensor comparison. -/
@[stacks 07A4 "monoidal pullback on good flat models", implicit_reducible]
noncomputable def monoidal :
    @Functor.Monoidal
      (HomotopyCategory.KFlat.TermwiseFlat
        (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY))) _
      (@ObjectProperty.fullMonoidalSubcategory _ _ _ _
        (CategoryTheory.HomotopyCategory.KFlat.TermwiseFlat.isMonoidal
          (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY))))
      (HomotopyCategory.KFlat.TermwiseFlat
        (ModuleCat.{w} (RingedSite.ofCommRingSheaf JX OX))) _
      (@ObjectProperty.fullMonoidalSubcategory _ _ _ _
        (CategoryTheory.HomotopyCategory.KFlat.TermwiseFlat.isMonoidal
          (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf JX OX))))
      (goodModels f) :=
  @Functor.CoreMonoidal.toMonoidal
    (HomotopyCategory.KFlat.TermwiseFlat
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY))) _
    (@ObjectProperty.fullMonoidalSubcategory _ _ _ _
      (CategoryTheory.HomotopyCategory.KFlat.TermwiseFlat.isMonoidal
        (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY))))
    (HomotopyCategory.KFlat.TermwiseFlat
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JX OX))) _
    (@ObjectProperty.fullMonoidalSubcategory _ _ _ _
      (CategoryTheory.HomotopyCategory.KFlat.TermwiseFlat.isMonoidal
        (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf JX OX))))
    (goodModels f) (coreMonoidal f)

/-- The canonical unit isomorphism for pullback on good flat models. -/
noncomputable abbrev unitIso :=
  @Functor.CoreMonoidal.εIso
    (HomotopyCategory.KFlat.TermwiseFlat
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY))) _
    (@ObjectProperty.fullMonoidalSubcategory _ _ _ _
      (CategoryTheory.HomotopyCategory.KFlat.TermwiseFlat.isMonoidal
        (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY))))
    (HomotopyCategory.KFlat.TermwiseFlat
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JX OX))) _
    (@ObjectProperty.fullMonoidalSubcategory _ _ _ _
      (CategoryTheory.HomotopyCategory.KFlat.TermwiseFlat.isMonoidal
        (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf JX OX))))
    (goodModels f) (coreMonoidal f)

/-- The canonical tensorator for pullback on good flat models. -/
@[stacks 07A4 "good-model pullback tensorator"]
noncomputable abbrev tensorIso
  (K L : HomotopyCategory.KFlat.TermwiseFlat
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY))) :=
  @Functor.CoreMonoidal.μIso
    (HomotopyCategory.KFlat.TermwiseFlat
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY))) _
    (@ObjectProperty.fullMonoidalSubcategory _ _ _ _
      (CategoryTheory.HomotopyCategory.KFlat.TermwiseFlat.isMonoidal
        (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY))))
    (HomotopyCategory.KFlat.TermwiseFlat
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JX OX))) _
    (@ObjectProperty.fullMonoidalSubcategory _ _ _ _
      (CategoryTheory.HomotopyCategory.KFlat.TermwiseFlat.isMonoidal
        (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf JX OX))))
    (goodModels f) (coreMonoidal f) K L

end goodModels

end RingedSite.Hom.modulePullbackHomotopy
