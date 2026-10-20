/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.DualObstruction.VersalAt
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.GroupoidsOver

universe u

/- Situation 98.24.2: let S be a locally Noetherian scheme and let X be a
category fibred in groupoids over (Sch/S)_fppf with (RS*), so that the functor
T_x(-) is available. Let U = Spec(A) be affine of finite type over S, mapping
into an affine open Spec(Λ), and let x be an object of X over U. Dual
obstruction data at this x consists of a complex K of A-modules, an
isomorphism T_x(-) ≅ H^1(K ⊗^L_A -), and obstruction classes
o_x(A') ∈ H^2(K ⊗^L_A I) for deformation situations (x, A' → A), natural in
square-zero extensions of A and vanishing if and only if x
lifts. Infinitesimal automorphisms Inf_x ≅ H^0(K ⊗^L_A -) are deliberately
omitted. Lean records this situation as DualObstruction. -/
@[stacks 07YX]
#check (AlgebraicGeometry.GroupoidsOver.DualObstruction :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] (X : GroupoidsOver S)
    [AlgebraicGeometry.GroupoidsOver.HasStrongRimSchlessinger X], Type (u + 1))

#check (AlgebraicGeometry.GroupoidsOver.DualObstruction.spec :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X] (𝒟 : DualObstruction X),
    LocallyOfFiniteType 𝒟.toS ∧ QuasiCompact 𝒟.toS ∧
      (Spec.map (CommRingCat.ofHom (algebraMap 𝒟.base 𝒟.carrier)) ≫
          𝒟.openImmersion = 𝒟.toS) ∧
      IsIso 𝒟.tangentIso.hom ∧
      (∀ {σ τ : DeformationSituation X}
          (hσ : σ.IsOver 𝒟.toObjectOverSpec) (hτ : τ.IsOver 𝒟.toObjectOverSpec)
          (f : DeformationSituation.Hom σ τ)
          (hf : f.toRingHom = DeformationSituation.ringHomIdOver hσ hτ),
          (homologyTensor 𝒟.complex 2).map
              (DeformationSituation.kernelMapOver hσ hτ f hf) (𝒟.obstruction hσ) =
            𝒟.obstruction hτ) ∧
      ∀ {σ : DeformationSituation X} (hσ : σ.IsOver 𝒟.toObjectOverSpec),
        Nonempty (DeformationSituation.ObjectLift σ) ↔ 𝒟.obstruction hσ = 0)

#check (AlgebraicGeometry.GroupoidsOver.DualObstruction.obstruction_eq_zero_iff_nonempty_objectLift :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [AlgebraicGeometry.GroupoidsOver.HasStrongRimSchlessinger X]
    (𝒟 : AlgebraicGeometry.GroupoidsOver.DualObstruction X)
    {σ : AlgebraicGeometry.GroupoidsOver.DeformationSituation X}
    (hσ : σ.IsOver 𝒟.toObjectOverSpec),
    𝒟.obstruction hσ = 0 ↔
      Nonempty (AlgebraicGeometry.GroupoidsOver.DeformationSituation.ObjectLift σ))
