/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap91.Lemma_91_13_1_Diagram
public import stacks_project.Chap91.Lemma_91_13_3
public import stacks_project.Chap91.Lemma_91_13_4
public import stacks_project.Chap91.Lemma_91_13_6_Map
import Mathlib.Tactic.CrossRefAttribute

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

/-- The identity-base connecting diagram of two square-zero `f⁻¹ O_B`-algebra
extensions, with `g = gSharp` and `ν` the adjunct of `c` transported along the
kernel identifications. -/
def ofIdentityBase (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F))
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    RelativeDiagram SC.proj (𝟙 O_B) SD.proj (𝟙 O_B) :=
  RelativeDiagram.of fSharp SC.structureMap SC.commutes
    (fSharp ≫ gSharp) SD.structureMap SD.commutes
    gSharp (𝟙 O_B) (𝟙 O_B) rfl (Category.id_comp (fSharp ≫ gSharp))
    (kernelIdealHom SC ≫ (extendRestrictAdj gSharp).homEquiv F G c ≫
      (restrictionAlong gSharp).map
        (SD.kernelIso.inv ≫ (idealTargetIso SD).inv))
    sorry

/-- `ofIdentityBase` has identity maps on `O_B`, `g = gSharp`, and `ν` the
adjunct of `c` transported along `kernelIdealHom`. -/
theorem ofIdentityBase_spec (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F))
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    (ofIdentityBase c SC SD).f1 = fSharp ∧
      (ofIdentityBase c SC SD).f2 = fSharp ≫ gSharp ∧
      (ofIdentityBase c SC SD).f1' = SC.structureMap ∧
      (ofIdentityBase c SC SD).f2' = SD.structureMap ∧
      (ofIdentityBase c SC SD).g = gSharp ∧
      (ofIdentityBase c SC SD).t = 𝟙 O_B ∧
      (ofIdentityBase c SC SD).t' = 𝟙 O_B ∧
      (ofIdentityBase c SC SD).ν =
        kernelIdealHom SC ≫ (extendRestrictAdj gSharp).homEquiv F G c ≫
          (restrictionAlong gSharp).map
            (SD.kernelIso.inv ≫ (idealTargetIso SD).inv) := sorry

end RelativeDiagram

namespace Solution

/-- Lemma 91.13.6 Let f : (Sh(C), O_C) ⟶ (Sh(B), O_B) and
g : (Sh(D), O_D) ⟶ (Sh(C), O_C) be morphisms of ringed topoi. Let F be an
O_C-module, G an O_D-module, and c : (extendAlong gSharp).obj F ⟶ G an
O_D-linear map. Let 0 ⟶ F ⟶ O_{C'} ⟶ O_C ⟶ 0 be an extension of
f⁻¹ O_B-algebras corresponding to
ξ = (extensionEquiv fSharp F).symm (isoClassMk SC), and
0 ⟶ G ⟶ O_{D'} ⟶ O_D ⟶ 0 an extension of g⁻¹ f⁻¹ O_B-algebras corresponding
to ζ = (extensionEquiv (fSharp ≫ gSharp) G).symm (isoClassMk SD). Then there
is a morphism g' : (Sh(D), O_{D'}) ⟶ (Sh(C), O_{C'}) of ringed topoi over
(Sh(B), O_B) compatible with g and c if and only if extOne_map c ξ equals
extOne_comap fSharp gSharp ζ in Ext⁽1⁾(Lg^* NL_{O_C/O_B}, G). -/
@[stacks 0GQ7]
theorem fittingMap_nonempty_iff (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F))
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    Nonempty (FittingMap (RelativeDiagram.ofIdentityBase c SC SD)) ↔
      extOne_map c ((extensionEquiv fSharp F).symm (isoClassMk SC)) =
        extOne_comap fSharp gSharp
          ((extensionEquiv (fSharp ≫ gSharp) G).symm (isoClassMk SD)) :=
  sorry

end Solution

end SheafOfModules.RingedSite.FirstOrderThickening
