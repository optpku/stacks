/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Kunneth.SingleSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal

/-!
# Cup products and the single-sheaf Künneth map

This file relates cup products by cohomology classes to the global Künneth morphism for module
sheaves placed in degree zero.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open RingedSpace.ModuleDerived RingedSpace.Module.Derived
open RingedSite.Hom.DerivedAdjunction
open Scheme.ModuleDerived.Kunneth

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Kunneth.SingleSheaf

variable {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

variable [KFlat.HomotopyTensorDescends X.toRingedSpace]
variable [KFlat.TensorDescends X.toRingedSpace]
variable [KFlat.IsLocalization X.toRingedSpace]
variable [HomotopyCategory.KFlat.HasResolutions X.toRingedSpace.Modules]
variable [∀ G₁ G₂ : GradedObject ℤ X.toRingedSpace.Modules,
  GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ X.toRingedSpace.Modules,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ X.toRingedSpace.Modules,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ X.toRingedSpace.Modules,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [KFlat.HomotopyTensorDescends (Limits.pullback a b).toRingedSpace]
variable [KFlat.TensorDescends (Limits.pullback a b).toRingedSpace]
variable [KFlat.IsLocalization (Limits.pullback a b).toRingedSpace]
variable [HomotopyCategory.KFlat.HasResolutions
  (Limits.pullback a b).toRingedSpace.Modules]
variable [∀ G₁ G₂ : GradedObject ℤ (Limits.pullback a b).toRingedSpace.Modules,
  GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Limits.pullback a b).toRingedSpace.Modules,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Limits.pullback a b).toRingedSpace.Modules,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ :
  GradedObject ℤ (Limits.pullback a b).toRingedSpace.Modules,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [KFlat.HomotopyTensorDescends S.toRingedSpace]
variable [KFlat.TensorDescends S.toRingedSpace]
variable [KFlat.IsLocalization S.toRingedSpace]

variable [HasPair (RingedSpace.opensRingedSiteHom a.toShHom)]
variable [HasPair (RingedSpace.opensRingedSiteHom b.toShHom)]
variable [HasPair
  (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b).toShHom)]
variable [HasPair
  (RingedSpace.opensRingedSiteHom (Limits.pullback.snd a b).toShHom)]
variable [HasPair
  (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b ≫ a).toShHom)]
variable [HasPair
  (RingedSpace.opensRingedSiteHom (Limits.pullback.snd a b ≫ b).toShHom)]
variable [HasPair (RingedSpace.opensRingedSiteHom
  ((Limits.pullback.fst a b).toShHom ≫ a.toShHom))]
variable [HasPair (RingedSpace.opensRingedSiteHom
  ((Limits.pullback.snd a b).toShHom ≫ b.toShHom))]

variable [IsIso (RingedSpace.modulePullbackDerived.compComparison
  (Limits.pullback.fst a b).toShHom a.toShHom)]
variable [IsIso (RingedSpace.modulePullbackDerived.compComparison
  (Limits.pullback.snd a b).toShHom b.toShHom)]
variable [(RingedSpace.modulePullbackDerived
  (Limits.pullback.fst a b ≫ a).toShHom).OplaxMonoidal]
variable [MonoidalCategory (Tensor.globalSectionsDerived S.toRingedSpace)]
variable [(GlobalSections.functor S.toRingedSpace).LaxMonoidal]

/-- Cup product by a class on the left factor commutes with the global Künneth morphism for
module sheaves placed in degree zero. -/
theorem map_leftCupBy_commSq
    (F G : X.Modules) (E : Y.Modules) (i : ℤ)
    [((tensoringRight (DerivedCategory X.Modules)).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj F)).CommShift ℤ]
    [((tensoringRight (Tensor.globalSectionsDerived S.toRingedSpace)).obj
      ((GlobalSections.functor S.toRingedSpace).obj
        ((RingedSpace.moduleDerivedPushforward b.toShHom).obj
          ((DerivedCategory.singleFunctor Y.Modules 0).obj E)))).CommShift ℤ]
    [(RingedSpace.moduleDerivedPushforward a.toShHom).CommShift ℤ]
    [(RingedSpace.moduleDerivedPushforward
      (Limits.pullback.fst a b ≫ a).toShHom).CommShift ℤ]
    [(RingedSpace.modulePullbackDerived
      (Limits.pullback.fst a b).toShHom).CommShift ℤ]
    [(RingedSpace.modulePullbackDerived
      (Limits.pullback.fst a b).toShHom).Monoidal]
    [((tensoringRight (RingedSpace.ModuleDerived
      (Limits.pullback a b).toRingedSpace)).obj
      ((DerivedCategory.singleFunctor (Limits.pullback a b).Modules 0).obj
        (Scheme.Modules.externalTensorProduct a b F E))).CommShift ℤ]
    (ξ : (𝟙_ (DerivedCategory X.Modules))⟦-i⟧ ⟶
      (DerivedCategory.singleFunctor X.Modules 0).obj G) :
    let F₀ := (DerivedCategory.singleFunctor X.Modules 0).obj F
    let G₀ := (DerivedCategory.singleFunctor X.Modules 0).obj G
    let E₀ := (DerivedCategory.singleFunctor Y.Modules 0).obj E
    let GF₀ := (DerivedCategory.singleFunctor X.Modules 0).obj (G ⊗ F)
    let p := Limits.pullback.fst a b
    let q := Limits.pullback.snd a b
    let c := p ≫ a
    let pull := RingedSpace.modulePullbackDerived p.toShHom
    let pF := (Scheme.Modules.pullback p).obj F
    let pG := (Scheme.Modules.pullback p).obj G
    let qE := (Scheme.Modules.pullback q).obj E
    let FE := Scheme.Modules.externalTensorProduct a b F E
    let GFE := (Scheme.Modules.pullback p).obj (G ⊗ F) ⊗ qE
    let pG₀ := (DerivedCategory.singleFunctor
      (Limits.pullback a b).Modules 0).obj pG
    let FE₀ := (DerivedCategory.singleFunctor
      (Limits.pullback a b).Modules 0).obj FE
    let GFE₀ := (DerivedCategory.singleFunctor
      (Limits.pullback a b).Modules 0).obj GFE
    let RΓX := RingedSpace.moduleDerivedPushforward a.toShHom ⋙
      GlobalSections.functor S.toRingedSpace
    let RΓY := RingedSpace.moduleDerivedPushforward b.toShHom ⋙
      GlobalSections.functor S.toRingedSpace
    let RΓP := RingedSpace.moduleDerivedPushforward c.toShHom ⋙
      GlobalSections.functor S.toRingedSpace
    let leftCupBy : F₀⟦-i⟧ ⟶ GF₀ :=
      ((λ_ F₀).inv)⟦-i⟧' ≫
        (((tensoringRight (DerivedCategory X.Modules)).obj F₀).commShiftIso (-i)).inv.app
          (𝟙_ (DerivedCategory X.Modules)) ≫
        (ξ ⊗ₘ 𝟙 F₀) ≫
        tensorComparison G F
    let pullξ : (𝟙_ (RingedSpace.ModuleDerived
        (Limits.pullback a b).toRingedSpace))⟦-i⟧ ⟶ pG₀ :=
      ((Functor.Monoidal.εIso pull).hom)⟦-i⟧' ≫
        (pull.commShiftIso (-i)).inv.app (𝟙_ (DerivedCategory X.Modules)) ≫
        pull.map ξ ≫
        pullbackComparison p G
    let bottomCupBy : FE₀⟦-i⟧ ⟶ GFE₀ :=
      ((λ_ FE₀).inv)⟦-i⟧' ≫
        (((tensoringRight (RingedSpace.ModuleDerived
          (Limits.pullback a b).toRingedSpace)).obj FE₀).commShiftIso
            (-i)).inv.app (𝟙_ (RingedSpace.ModuleDerived
              (Limits.pullback a b).toRingedSpace)) ≫
        pullξ ▷ FE₀ ≫
        tensorComparison pG FE ≫
        (DerivedCategory.singleFunctor (Limits.pullback a b).Modules 0).map
          ((α_ pG pF qE).inv ≫
            (Scheme.Modules.pullbackTensorIso p G F).inv ▷ qE)
    CommSq
      ((RΓX.commShiftIso (-i)).inv.app F₀ ≫ RΓX.map leftCupBy ⊗ₘ 𝟙 (RΓY.obj E₀))
      ((((tensoringRight (Tensor.globalSectionsDerived S.toRingedSpace)).obj
        ((GlobalSections.functor S.toRingedSpace).obj
          ((RingedSpace.moduleDerivedPushforward b.toShHom).obj E₀))).commShiftIso
          (-i)).hom.app
            ((GlobalSections.functor S.toRingedSpace).obj
              ((RingedSpace.moduleDerivedPushforward a.toShHom).obj F₀)) ≫
        (globalMap a b F₀ E₀ ≫
          RΓP.map (externalTensorComparison a b F E))⟦-i⟧')
      (globalMap a b GF₀ E₀ ≫
        RΓP.map (externalTensorComparison a b (G ⊗ F) E))
      ((RΓP.commShiftIso (-i)).inv.app FE₀ ≫ RΓP.map bottomCupBy) := sorry

end AlgebraicGeometry.Scheme.Modules.Kunneth.SingleSheaf
