/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.ObstructionTheory
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.GroupoidsOver

universe u

/- Definition 98.22.1: let S be a locally Noetherian base and let X be a
category fibred in groupoids over (Sch/S)_fppf. An obstruction theory is extra
data: for every S-algebra A such that Spec(A) ⟶ S maps into an affine open and
every object x of X over Spec(A), an A-linear functor O_x : Mod_A ⥤ Mod_A of
obstruction modules; for a ring map A → B, modules M, N, and an A-linear map
M ⟶ N, an induced A-linear map O_x(M) ⟶ O_y(N) where y = x|_Spec(B); and for
every deformation situation (x, A' → A) an obstruction o_x(A') ∈ O_x(I) with
I = Ker(A' → A). These data make (x, A, M) ↦ O_x(M) a functor to sets, send
obstructions to obstructions along morphisms of deformation situations, and
satisfy Lift(x, A') nonempty iff o_x(A') = 0. -/
@[stacks 07YG] #check (AlgebraicGeometry.GroupoidsOver.ObstructionTheory :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S],
    AlgebraicGeometry.GroupoidsOver S → Type (u + 1))

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}

#check (AlgebraicGeometry.GroupoidsOver.ObstructionTheory.spec :
  ∀ (𝒪 : ObstructionTheory X),
    (∀ ξ : ObjectOverSpec X, (𝒪.module ξ).ModuleLinear ξ.carrier) ∧
      (∀ ξ : ObstructionTriple X,
        𝒪.map (ObstructionTriple.Hom.id ξ) =
          (ModuleCat.restrictScalarsId ξ.carrier).inv.app
            ((𝒪.module ξ.toObjectOverSpec).obj ξ.M)) ∧
      (∀ {ξ η ζ : ObstructionTriple X} (f : ObstructionTriple.Hom ξ η)
          (g : ObstructionTriple.Hom η ζ),
        𝒪.map (ObstructionTriple.Hom.comp f g) =
          𝒪.map f ≫ (ModuleCat.restrictScalars f.toRingHom).map (𝒪.map g) ≫
            (ModuleCat.restrictScalarsComp' f.toRingHom g.toRingHom
              (g.toRingHom.comp f.toRingHom) rfl).inv.app
              ((𝒪.module ζ.toObjectOverSpec).obj ζ.M)) ∧
      (∀ (ξ : ObjectOverSpec X) {M N : ModuleCat.{u} ξ.carrier} (f : M ⟶ N),
        𝒪.map (ObstructionTriple.Hom.ofModuleHom ξ f) =
          (𝒪.module ξ).map f ≫
            (ModuleCat.restrictScalarsId ξ.carrier).inv.app ((𝒪.module ξ).obj N)) ∧
      (∀ {σ τ : DeformationSituation X} (f : DeformationSituation.Hom σ τ),
        𝒪.map f.toTripleHom (𝒪.obstruction σ) = 𝒪.obstruction τ) ∧
      ∀ σ : DeformationSituation X,
        Nonempty (DeformationSituation.ObjectLift σ) ↔ 𝒪.obstruction σ = 0)

#check (AlgebraicGeometry.GroupoidsOver.ObstructionTheory.obstruction_eq_zero_iff_nonempty_objectLift :
  ∀ (𝒪 : ObstructionTheory X) (σ : DeformationSituation X),
    𝒪.obstruction σ = 0 ↔ Nonempty (DeformationSituation.ObjectLift σ))
