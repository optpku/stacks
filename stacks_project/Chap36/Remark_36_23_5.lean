module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Kunneth.SingleSheaf.CupProduct

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open RingedSpace.ModuleDerived RingedSpace.Module.Derived
open RingedSite.Hom.DerivedAdjunction
open Scheme.ModuleDerived.Kunneth

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Modules
namespace Kunneth

variable (A : Type u) [CommRing A]
variable {X Y : Scheme.{u}}
variable (a : X ⟶ Spec (CommRingCat.of A)) (b : Y ⟶ Spec (CommRingCat.of A))

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
variable [KFlat.HomotopyTensorDescends
  (Limits.pullback a b).toRingedSpace]
variable [KFlat.TensorDescends
  (Limits.pullback a b).toRingedSpace]
variable [KFlat.IsLocalization
  (Limits.pullback a b).toRingedSpace]
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
variable [KFlat.HomotopyTensorDescends
  (Spec (CommRingCat.of A)).toRingedSpace]
variable [KFlat.TensorDescends
  (Spec (CommRingCat.of A)).toRingedSpace]
variable [KFlat.IsLocalization
  (Spec (CommRingCat.of A)).toRingedSpace]

variable [HasPair
  (RingedSpace.opensRingedSiteHom a.toShHom)]
variable [HasPair
  (RingedSpace.opensRingedSiteHom b.toShHom)]
variable [HasPair
  (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b).toShHom)]
variable [HasPair
  (RingedSpace.opensRingedSiteHom (Limits.pullback.snd a b).toShHom)]
variable [HasPair
  (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b ≫ a).toShHom)]
variable [HasPair
  (RingedSpace.opensRingedSiteHom (Limits.pullback.snd a b ≫ b).toShHom)]
variable [HasPair
  (RingedSpace.opensRingedSiteHom
    ((Limits.pullback.fst a b).toShHom ≫ a.toShHom))]
variable [HasPair
  (RingedSpace.opensRingedSiteHom
    ((Limits.pullback.snd a b).toShHom ≫ b.toShHom))]

variable [IsIso (RingedSpace.modulePullbackDerived.compComparison
  (Limits.pullback.fst a b).toShHom a.toShHom)]
variable [IsIso (RingedSpace.modulePullbackDerived.compComparison
  (Limits.pullback.snd a b).toShHom b.toShHom)]
variable [(RingedSpace.modulePullbackDerived
  (Limits.pullback.fst a b ≫ a).toShHom).OplaxMonoidal]
variable [MonoidalCategory
  (Tensor.globalSectionsDerived
    (Spec (CommRingCat.of A)).toRingedSpace)]
variable [(GlobalSections.functor
  (Spec (CommRingCat.of A)).toRingedSpace).LaxMonoidal]

variable (F G : Scheme.QCoh X) (E : Scheme.QCoh Y) (i : ℤ)
variable [((tensoringRight (DerivedCategory X.Modules)).obj
  ((DerivedCategory.singleFunctor X.Modules 0).obj F.obj)).CommShift ℤ]
variable [((tensoringRight (Tensor.globalSectionsDerived
  (Spec (CommRingCat.of A)).toRingedSpace)).obj
    ((GlobalSections.functor (Spec (CommRingCat.of A)).toRingedSpace).obj
      ((RingedSpace.moduleDerivedPushforward b.toShHom).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj E.obj)))).CommShift ℤ]
variable [(RingedSpace.moduleDerivedPushforward a.toShHom).CommShift ℤ]
variable [(RingedSpace.moduleDerivedPushforward
  (Limits.pullback.fst a b ≫ a).toShHom).CommShift ℤ]
variable [(RingedSpace.modulePullbackDerived
  (Limits.pullback.fst a b).toShHom).CommShift ℤ]
variable [(RingedSpace.modulePullbackDerived
  (Limits.pullback.fst a b).toShHom).Monoidal]
variable [((tensoringRight (RingedSpace.ModuleDerived
  (Limits.pullback a b).toRingedSpace)).obj
  ((DerivedCategory.singleFunctor (Limits.pullback a b).Modules 0).obj
    (Scheme.Modules.externalTensorProduct a b F.obj E.obj))).CommShift ℤ]
variable (ξ : (𝟙_ (DerivedCategory X.Modules))⟦-i⟧ ⟶
  (DerivedCategory.singleFunctor X.Modules 0).obj G.obj)

/- Remark 36.23.5: let `S = Spec (CommRingCat.of A)`, let `a : X ⟶ S` and
`b : Y ⟶ S`, and let `F`, `G`, and `E` be quasicoherent modules on `X`, `X`, and
`Y`. If `ξ : (𝟙_ (DerivedCategory X.Modules))⟦-i⟧ ⟶ G[0]` represents a class in
`H^i(X, G)`, then cup product gives a commutative square from
`RΓ(X, F)[-i] ⊗ᴸ_A RΓ(Y, E)` to `RΓ(X, G ⊗ F) ⊗ᴸ_A RΓ(Y, E)` and from
`RΓ(X ×_S Y, p^*F ⊗ q^*E)[-i]` to
`RΓ(X ×_S Y, p^*(G ⊗ F) ⊗ q^*E)`. The bottom map uses the canonical
pullback of `ξ` and the degree-zero ordinary-tensor comparisons; the vertical maps are
the global Künneth maps followed by the derived-to-ordinary external-tensor comparisons. -/
@[stacks 0G7W]
#check
  (AlgebraicGeometry.Scheme.Modules.Kunneth.SingleSheaf.map_leftCupBy_commSq
      (S := Spec (CommRingCat.of A)) a b F.obj G.obj E.obj i ξ :
    let F₀ := (DerivedCategory.singleFunctor X.Modules 0).obj F.obj
    let G₀ := (DerivedCategory.singleFunctor X.Modules 0).obj G.obj
    let E₀ := (DerivedCategory.singleFunctor Y.Modules 0).obj E.obj
    let GF₀ := (DerivedCategory.singleFunctor X.Modules 0).obj (G.obj ⊗ F.obj)
    let p := Limits.pullback.fst a b
    let q := Limits.pullback.snd a b
    let c := p ≫ a
    let pull := RingedSpace.modulePullbackDerived p.toShHom
    let pF := (Scheme.Modules.pullback p).obj F.obj
    let pG := (Scheme.Modules.pullback p).obj G.obj
    let qE := (Scheme.Modules.pullback q).obj E.obj
    let FE := Scheme.Modules.externalTensorProduct a b F.obj E.obj
    let GFE := (Scheme.Modules.pullback p).obj (G.obj ⊗ F.obj) ⊗ qE
    let pG₀ := (DerivedCategory.singleFunctor
      (Limits.pullback a b).Modules 0).obj pG
    let FE₀ := (DerivedCategory.singleFunctor
      (Limits.pullback a b).Modules 0).obj FE
    let GFE₀ := (DerivedCategory.singleFunctor
      (Limits.pullback a b).Modules 0).obj GFE
    let RΓX := RingedSpace.moduleDerivedPushforward a.toShHom ⋙
      GlobalSections.functor (Spec (CommRingCat.of A)).toRingedSpace
    let RΓY := RingedSpace.moduleDerivedPushforward b.toShHom ⋙
      GlobalSections.functor (Spec (CommRingCat.of A)).toRingedSpace
    let RΓP := RingedSpace.moduleDerivedPushforward c.toShHom ⋙
      GlobalSections.functor (Spec (CommRingCat.of A)).toRingedSpace
    let leftCupBy : F₀⟦-i⟧ ⟶ GF₀ :=
      ((λ_ F₀).inv)⟦-i⟧' ≫
        (((tensoringRight (DerivedCategory X.Modules)).obj F₀).commShiftIso (-i)).inv.app
          (𝟙_ (DerivedCategory X.Modules)) ≫
        (ξ ⊗ₘ 𝟙 F₀) ≫
        SingleSheaf.tensorComparison G.obj F.obj
    let pullξ : (𝟙_ (RingedSpace.ModuleDerived
        (Limits.pullback a b).toRingedSpace))⟦-i⟧ ⟶
        pG₀ :=
      ((Functor.Monoidal.εIso pull).hom)⟦-i⟧' ≫
        (pull.commShiftIso (-i)).inv.app (𝟙_ (DerivedCategory X.Modules)) ≫
        pull.map ξ ≫
        SingleSheaf.pullbackComparison p G.obj
    let bottomCupBy :
        FE₀⟦-i⟧ ⟶ GFE₀ :=
      ((λ_ FE₀).inv)⟦-i⟧' ≫
        (((tensoringRight (RingedSpace.ModuleDerived
          (Limits.pullback a b).toRingedSpace)).obj
          FE₀).commShiftIso
            (-i)).inv.app (𝟙_ (RingedSpace.ModuleDerived
              (Limits.pullback a b).toRingedSpace)) ≫
        pullξ ▷ FE₀ ≫
        SingleSheaf.tensorComparison pG FE ≫
        (DerivedCategory.singleFunctor (Limits.pullback a b).Modules 0).map
          ((α_ pG pF qE).inv ≫
            (Scheme.Modules.pullbackTensorIso p G.obj F.obj).inv ▷ qE)
    CommSq
      ((RΓX.commShiftIso (-i)).inv.app F₀ ≫ RΓX.map leftCupBy ⊗ₘ 𝟙 (RΓY.obj E₀))
      ((((tensoringRight (Tensor.globalSectionsDerived
        (Spec (CommRingCat.of A)).toRingedSpace)).obj
          ((GlobalSections.functor
            (Spec (CommRingCat.of A)).toRingedSpace).obj
              ((RingedSpace.moduleDerivedPushforward b.toShHom).obj E₀))).commShiftIso
          (-i)).hom.app
            ((GlobalSections.functor
              (Spec (CommRingCat.of A)).toRingedSpace).obj
                ((RingedSpace.moduleDerivedPushforward a.toShHom).obj F₀)) ≫
        (globalMap a b F₀ E₀ ≫
          RΓP.map (SingleSheaf.externalTensorComparison a b F.obj E.obj))⟦-i⟧')
      (globalMap a b GF₀ E₀ ≫
        RΓP.map (SingleSheaf.externalTensorComparison a b (G.obj ⊗ F.obj) E.obj))
      ((RΓP.commShiftIso (-i)).inv.app
          FE₀ ≫
        RΓP.map bottomCupBy))

end Kunneth
end Modules
end Scheme
end AlgebraicGeometry

end
