/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.NaiveObstructionTheory
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.GroupoidsOver DerivedCategory

universe u

/- Definition 98.23.5: let S be a locally Noetherian base and let X be a
category fibred in groupoids over (Sch/S)_fppf satisfying (RS*). A naive
obstruction theory assigns, to every S-algebra A such that Spec(A) ⟶ S factors
through an affine open Spec(Λ) ⊂ S and every object x of X over Spec(A), a
complex E_x in D⁻(A) and a map ξ_x : E_x ⟶ NL{A⁄Λ}; isomorphisms of functors
Inf_x ≅ Ext^{-1}_A(E_x, -) and T_x ≅ Ext^0_A(E_x, -); and functoriality maps
E_x ⟶ E_y in D(A) along A → B with y = x|_Spec(B). These data make diagram (i)
commute, compose, match the maps of Remark 98.21.3, send ξ_x composed with
NL ⟶ Ω to the canonical element of T_x(Ω[A⁄Λ]), and detect lifts of a
deformation situation (x, A' → A) by vanishing of
E_x ⟶ NL{A⁄Λ} ⟶ NL{A⁄A'}. -/
@[stacks 07YP] #check
  (AlgebraicGeometry.GroupoidsOver.NaiveObstructionTheory :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] (X : GroupoidsOver S)
      [HasStrongRimSchlessinger X], Type (u + 1))

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {X : GroupoidsOver S} [HasStrongRimSchlessinger X]

#check (NaiveObstructionTheory.infIso_natural :
  ∀ (𝒪 : NaiveObstructionTheory X), ∀ {ξ η : ObjectOverAffineOpen X}
      (f : ObjectOverAffineOpen.Hom ξ η)
      {M : ModuleCat.{u} ξ.carrier} {N : ModuleCat.{u} η.carrier}
      (g : M ⟶ (ModuleCat.restrictScalars f.toRingHom).obj N),
    (𝒪.infIso ξ).hom.app M ≫
        (DerivedCategory.Ext.moduleFunctor (Minus.ι.obj (𝒪.complex ξ)) (-1)).map g =
      (ModuleCat.uliftFunctor.{u + 1, u} ξ.carrier).map
          (infMap (CommRingCat.ofHom f.toRingHom) f.toS_comp g
            ξ.toObjectOverSpec.toFiber η.toObjectOverSpec.toFiber f.fiberArrow) ≫
        (ModuleCat.uliftRestrictScalarsIso f.toRingHom).hom.app
          ((infFunctor η.toObjectOverSpec.toFiber).obj N) ≫
          (ModuleCat.restrictScalars.{u + 1} f.toRingHom).map ((𝒪.infIso η).hom.app N) ≫
            DerivedCategory.Ext.restrictionMap (𝒪.map f) (-1) N)

#check (NaiveObstructionTheory.tangentIso_natural :
  ∀ (𝒪 : NaiveObstructionTheory X), ∀ {ξ η : ObjectOverAffineOpen X}
      (f : ObjectOverAffineOpen.Hom ξ η)
      {M : ModuleCat.{u} ξ.carrier} {N : ModuleCat.{u} η.carrier}
      (g : M ⟶ (ModuleCat.restrictScalars f.toRingHom).obj N),
    (𝒪.tangentIso ξ).hom.app M ≫
        (DerivedCategory.Ext.moduleFunctor (Minus.ι.obj (𝒪.complex ξ)) (0 : ℤ)).map g =
      tangentMap (CommRingCat.ofHom f.toRingHom) f.toS_comp g
          ξ.toObjectOverSpec.toFiber η.toObjectOverSpec.toFiber f.fiberArrow ≫
        (ModuleCat.restrictScalars.{u + 1} f.toRingHom).map ((𝒪.tangentIso η).hom.app N) ≫
          DerivedCategory.Ext.restrictionMap (𝒪.map f) (0 : ℤ) N)

#check (NaiveObstructionTheory.canonical_compat :
  ∀ (𝒪 : NaiveObstructionTheory X), ∀ ξ : ObjectOverAffineOpen X,
    (DerivedCategory.Ext.moduleFunctor (Minus.ι.obj (𝒪.complex ξ)) (0 : ℤ)).map
          (ObjectOverAffineOpen.kaehlerCompare ξ)
        ((𝒪.tangentIso ξ).hom.app (CommRingCat.KaehlerDifferential ξ.algebraHom)
          (canonicalElement ξ.algebraHom ξ.factor ξ.toObjectOverSpec.toFiber
            ξ.isOpenImmersion)) =
      ShiftedHom.mk₀ (0 : ℤ) rfl (𝒪.obstructionMap ξ ≫ Algebra.NaiveCotangent.naiveCotangentToKaehler))

#check (NaiveObstructionTheory.lifts_iff :
  ∀ (𝒪 : NaiveObstructionTheory X), ∀ {ξ : ObjectOverAffineOpen X} (τ : DeformationSituation.OverAffine ξ),
    𝒪.obstructionMap ξ ≫
        @Algebra.NaiveCotangent.naiveCotangentMap ξ.base τ.situation.source ξ.carrier
          _ _ _ τ.algebra ξ.algebra τ.algHom = 0 ↔
      Nonempty (DeformationSituation.ObjectLift τ.situation))

