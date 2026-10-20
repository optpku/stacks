/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Stalk
public import stacks_project.Chap66.Lemma_66_19_9_Stalk
public import stacks_project.Chap66.«66_27_0_1_Comparison»
public import stacks_project.Chap66.«66_27_0_2_RingedSite»
import StacksCheckRecall

/-!
# Stalks of extension by zero on étale localizations of algebraic spaces

The additive stalk of localization lower shriek at a geometric point is the coproduct of
the additive stalks at the lifts of that point.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open SheafOfModules SheafOfModules.Localization

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X U : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
variable [(restriction (spacesStructureSheaf X) (spacesEtaleSite.mk j) :
    SheafOfModules.{u + 1} (spacesStructureSheaf X) ⥤
      SheafOfModules.{u + 1}
        ((spacesStructureSheaf X).over (spacesEtaleSite.mk j))).IsRightAdjoint]
variable [HasWeakSheafify (spacesEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [∀ P : (Over (spacesEtaleSite.mk j))ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (Over.forget (spacesEtaleSite.mk j)).op.HasLeftKanExtension P]
variable [LocallySmall.{u + 1} (spacesEtaleSite X)]
variable (xbar : GeometricPoint X)
variable (G : SheafOfModules.{u + 1}
  ((spacesStructureSheaf X).over (spacesEtaleSite.mk j)))

/- 75.10.0.2: for an étale morphism `j : U ⟶ X` of algebraic spaces over `S` and a module
`G` on the localized ringed site at `U`, the additive stalk of `j_{U!} G` at a geometric
point `xbar : Spec(k) ⟶ X` is the coproduct of the additive stalks of `G` at the lifts
`ū : Spec(k) ⟶ U` with `j ∘ ū = xbar`. The index type is
`(toSpacesEtalePoint xbar).fiber.obj (spacesEtaleSite.mk j)`. `G` lives on the localized
site, identified with modules on `U` by `spacesEtaleLocalizationIso`. -/
@[stacks 08GU]
#check
  (SheafOfModules.Localization.lowerShriek.underlyingFiber_isomorphic_coproduct
    (spacesStructureSheaf X) (spacesEtaleSite.mk j) (toSpacesEtalePoint xbar) G :
    IsIsomorphic
      ((lowerShriek (spacesStructureSheaf X) (spacesEtaleSite.mk j) ⋙
          toSheaf (spacesStructureSheaf X) ⋙
          ((toSpacesEtalePoint xbar).sheafFiber :
            Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
              AddCommGrpCat.{u + 1})).obj G)
      (∐ fun ū : (toSpacesEtalePoint xbar).fiber.obj (spacesEtaleSite.mk j) ↦
        (toSheaf ((spacesStructureSheaf X).over (spacesEtaleSite.mk j)) ⋙
            (((toSpacesEtalePoint xbar).over ū).sheafFiber :
              Sheaf ((spacesEtaleTopology X).over (spacesEtaleSite.mk j))
                AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1})).obj G))

end AlgebraicGeometry.AlgebraicSpace
