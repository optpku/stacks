/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.FittingMap
public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.MapObstruction
public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.AlgebraExtension
public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.ExtMap
public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.IsoClass

/-!
# Functoriality of square-zero f⁻¹O_B-algebra extensions of ringed topoi

A morphism of ringed topoi over `(Sh(B), O_B)` compatible with `g` and a
coefficient map `c : g^* F ⟶ G` exists if and only if the Ext¹ classes of
the two identity-base extensions agree in `Ext⁽1⁾(Lg^* NL_{O_C/O_B}, G)`.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening
open SheafOfModules.RingedSite.FirstOrderThickening.Solution
open SheafOfModules.RingedSite.NaiveCotangent
open scoped DerivedExt SheafOfModules.RingedSite

noncomputable section

set_option backward.privateInPublic true

universe u

namespace SheafOfModules.RingedSite.FirstOrderThickening

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, `singleFunctor`, and Ext must share that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf presentation uses the same standard derived-category owner, exposed through the site-level spelling.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O_B O_C O_D : Sheaf J CommRingCat.{u}}
variable {fSharp : O_B ⟶ O_C} {gSharp : O_C ⟶ O_D}
variable {F : SheafOfModules (ringSheaf J O_C)}
variable {G : SheafOfModules (ringSheaf J O_D)}

namespace RelativeDiagram

/-- The coefficient adjunct makes the kernel square over the identity base commute. -/
private theorem ofIdentityBase_kernelSquare (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F))
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    toAdditive fSharp (@inducedKernelMap _ _ _ _ _ _ _ _ _ _ _ _ _
      (𝟙 O_B) fSharp SC.proj SC.structureMap inferInstance
      SC.instIsFirstOrderThickening_sol SC.commutes) ≫
        toAdditive gSharp (kernelIdealHom SC ≫ (extendRestrictAdj gSharp).homEquiv F G c ≫
          (restrictionAlong gSharp).map (SD.kernelIso.inv ≫ (idealTargetIso SD).inv)) =
      toAdditive (𝟙 O_B) (inducedKernelMap (𝟙 O_B) (𝟙 O_B) (𝟙 O_B)
        (𝟙 O_B) rfl) ≫
        toAdditive (fSharp ≫ gSharp) (@inducedKernelMap _ _ _ _ _ _ _ _ _ _ _ _ _
          (𝟙 O_B) (fSharp ≫ gSharp) SD.proj SD.structureMap inferInstance
          SD.instIsFirstOrderThickening_sol SD.commutes) := sorry

/-- The identity-base connecting diagram of two square-zero `f⁻¹ O_B`-algebra
extensions, with `g = gSharp` and `ν` the adjunct of `c` transported along the
kernel identifications. -/
def ofIdentityBase (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F))
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    RelativeDiagram SC.proj (𝟙 O_B) SD.proj (𝟙 O_B)
      (hπO1 := SC.instIsFirstOrderThickening_sol)
      (hπO2 := SD.instIsFirstOrderThickening_sol) :=
  RelativeDiagram.of
    (hπO1 := SC.instIsFirstOrderThickening_sol)
    (hπO2 := SD.instIsFirstOrderThickening_sol) fSharp SC.structureMap SC.commutes
    (fSharp ≫ gSharp) SD.structureMap SD.commutes
    gSharp (𝟙 O_B) (𝟙 O_B) rfl (Category.id_comp (fSharp ≫ gSharp))
    (kernelIdealHom SC ≫ (extendRestrictAdj gSharp).homEquiv F G c ≫
      (restrictionAlong gSharp).map
        (SD.kernelIso.inv ≫ (idealTargetIso SD).inv))
    (ofIdentityBase_kernelSquare c SC SD)

/-- `ofIdentityBase` has identity maps on `O_B`, `g = gSharp`, and `ν` the
adjunct of `c` transported along `kernelIdealHom`. -/
theorem ofIdentityBase_spec (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F))
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    (ofIdentityBase c SC SD).f1
        (hπO1 := SC.instIsFirstOrderThickening_sol)
        (hπO2 := SD.instIsFirstOrderThickening_sol) = fSharp ∧
      (ofIdentityBase c SC SD).f2
        (hπO1 := SC.instIsFirstOrderThickening_sol)
        (hπO2 := SD.instIsFirstOrderThickening_sol) = fSharp ≫ gSharp ∧
      (ofIdentityBase c SC SD).f1'
        (hπO1 := SC.instIsFirstOrderThickening_sol)
        (hπO2 := SD.instIsFirstOrderThickening_sol) = SC.structureMap ∧
      (ofIdentityBase c SC SD).f2'
        (hπO1 := SC.instIsFirstOrderThickening_sol)
        (hπO2 := SD.instIsFirstOrderThickening_sol) = SD.structureMap ∧
      (ofIdentityBase c SC SD).g
        (hπO1 := SC.instIsFirstOrderThickening_sol)
        (hπO2 := SD.instIsFirstOrderThickening_sol) = gSharp ∧
      (ofIdentityBase c SC SD).t
        (hπO1 := SC.instIsFirstOrderThickening_sol)
        (hπO2 := SD.instIsFirstOrderThickening_sol) = 𝟙 O_B ∧
      (ofIdentityBase c SC SD).t'
        (hπO1 := SC.instIsFirstOrderThickening_sol)
        (hπO2 := SD.instIsFirstOrderThickening_sol) = 𝟙 O_B ∧
      (ofIdentityBase c SC SD).ν
        (hπO1 := SC.instIsFirstOrderThickening_sol)
        (hπO2 := SD.instIsFirstOrderThickening_sol) =
        kernelIdealHom SC ≫ (extendRestrictAdj gSharp).homEquiv F G c ≫
          (restrictionAlong gSharp).map
            (SD.kernelIso.inv ≫ (idealTargetIso SD).inv) := sorry

end RelativeDiagram

namespace Solution

/-- Two square-zero algebra extensions admit a fitting morphism precisely when their
classes have equal images under cotangent and coefficient transport. -/
theorem fittingMap_nonempty_iff (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F))
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    Nonempty (FittingMap (RelativeDiagram.ofIdentityBase c SC SD)
      (hπO1 := SC.instIsFirstOrderThickening_sol)
      (hπO2 := SD.instIsFirstOrderThickening_sol)) ↔
      extOne_map c ((extensionEquiv fSharp F).symm (isoClassMk SC)) =
        extOne_comap fSharp gSharp
          ((extensionEquiv (fSharp ≫ gSharp) G).symm (isoClassMk SD)) := sorry

end Solution

end SheafOfModules.RingedSite.FirstOrderThickening
