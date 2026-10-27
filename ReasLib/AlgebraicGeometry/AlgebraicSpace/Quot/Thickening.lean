/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.Scheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Functorial
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal

/-! # Fibre thickenings and their ideal comparisons -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The square comparing `X_T ⊂ X_{T'}` with `T ⊂ T'` over `B`. -/
theorem fiberMap_commSq (f : X ⟶ B) {σ σ' : SchemeOver B} (h : σ ⟶ σ') :
    CommSq (pullback.snd f σ.hom) (fiberMap f h)
      ((ofOverFunctor S).map h.left) (pullback.snd f σ'.hom) :=
  sorry

/-- A first-order thickening `T ⊂ T'` of schemes over `B` induces a
first-order thickening `X_T ⊂ X_{T'}`. -/
instance instIsFirstOrderThickening_fiberMap (f : X ⟶ B) {σ σ' : SchemeOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left] :
    IsFirstOrderThickening (fiberMap f h) :=
  sorry

/-- The pullback `f_T^* J` of the ideal sheaf of `T ⊂ T'` to `X_T`. -/
def pullbackIdeal (f : X ⟶ B) {σ σ' : SchemeOver B} (h : σ ⟶ σ') :
    (fiber f σ).Modules :=
  (Modules.pullback (pullback.snd f σ.hom)).obj
    ((Modules.pullback ((ofOverFunctor S).map h.left)).obj
      (Hom.idealSheaf ((ofOverFunctor S).map h.left)))

/-- The comparison `f_T^* J ⟶ i^* I` identifying the ideal sheaf of `X_T ⊂ X_{T'}` as a
quotient of `f_T^* J`. -/
def idealComparison (f : X ⟶ B) {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left] :
    pullbackIdeal f h ⟶
      (Modules.pullback (fiberMap f h)).obj (Hom.idealSheaf (fiberMap f h)) :=
  (Modules.pullbackCompIso (pullback.snd f σ.hom) ((ofOverFunctor S).map h.left)).hom.app
      (Hom.idealSheaf ((ofOverFunctor S).map h.left)) ≫
    eqToHom
      (congrArg (fun k ↦ (Modules.pullback k).obj
          (Hom.idealSheaf ((ofOverFunctor S).map h.left)))
        (fiberMap_snd f h).symm) ≫
    (Modules.pullbackCompIso (fiberMap f h) (pullback.snd f σ'.hom)).inv.app
      (Hom.idealSheaf ((ofOverFunctor S).map h.left)) ≫
    (Modules.pullback (fiberMap f h)).map
      (Hom.Conormal.pulledIdealToIdeal (fiberMap_commSq f h))

/-- The comparison `f_T^* J ⟶ i^* I` is an epimorphism, so `I` is a quotient of
`f_T^* J`. -/
theorem epi_idealComparison (f : X ⟶ B) {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left] :
    _root_.CategoryTheory.Epi (idealComparison f h) :=
  sorry

/-- The coefficient module `G ⊗_{O_T} J`, defined as `G ⊗_{O_{X_T}} f_T^* J`. -/
abbrev tensorIdeal (f : X ⟶ B) {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    (G : (fiber f σ).Modules) : (fiber f σ).Modules :=
  tensorObj G (pullbackIdeal f h)

/-- Tensoring with `f_T^* J` is functorial in the `O_{X_T}`-module. -/
def tensorIdeal_map (f : X ⟶ B) {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    {G H : (fiber f σ).Modules} (φ : G ⟶ H) :
    tensorIdeal f h G ⟶ tensorIdeal f h H :=
  tensorHom φ (𝟙 (pullbackIdeal f h))

/-- The comparison `G ⊗ f_T^* J ⟶ G ⊗ i^* I` induced by `idealComparison`. -/
def tensorIdeal_comparison (f : X ⟶ B) {σ σ' : SchemeOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (G : (fiber f σ).Modules) :
    tensorIdeal f h G ⟶
      tensorObj G ((Modules.pullback (fiberMap f h)).obj (Hom.idealSheaf (fiberMap f h))) :=
  tensorHom (𝟙 G) (idealComparison f h)

end AlgebraicGeometry.AlgebraicSpace.Quot
