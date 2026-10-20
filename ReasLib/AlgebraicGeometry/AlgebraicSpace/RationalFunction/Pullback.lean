/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood

/-! # Pullback of rational functions along morphisms preserving dense opens -/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A morphism of algebraic spaces preserves dense opens when the pullback of every
dense open subspace remains dense. -/
def PreservesDenseOpens {X Y : AlgebraicSpace S} (f : Y ⟶ X) : Prop :=
  ∀ (U : smallZariskiSite X), IsDense U.hom → IsDense (domainInfFst f U.hom)

/-- The structure morphism of an elementary étale neighbourhood preserves dense opens. -/
theorem preservesDenseOpens_of_elementary {X : AlgebraicSpace S} {x : Points X}
    (U : EtaleNeighborhood.Elementary X x) : PreservesDenseOpens U.obj.hom :=
  sorry

/-- The fibre product of an open immersion along an arbitrary morphism remains an
open immersion. -/
theorem isOpenImmersion_domainInfFst {X Y : AlgebraicSpace S} {f : Y ⟶ X}
    (U : smallZariskiSite X) :
    IsOpenImmersion (domainInfFst f U.hom) :=
  sorry

/-- Pull back a partial map along a morphism that preserves dense opens, using the
fibre product of the domain with the source. -/
def PartialMap.precomp {X Y Z : AlgebraicSpace S} (φ : PartialMap X Z) {f : Y ⟶ X}
    (hf : PreservesDenseOpens f) : PartialMap Y Z where
  domain :=
    MorphismProperty.Over.mk ⊤ (domainInfFst f φ.domain.hom)
      (isOpenImmersion_domainInfFst φ.domain)
  dense_domain := hf φ.domain φ.dense_domain
  hom := domainInfSnd f φ.domain.hom ≫ φ.hom

/-- Precomposition of equivalent partial maps yields equivalent partial maps. -/
theorem PartialMap.precomp_toRationalMap_respects {X Y : AlgebraicSpace S}
    {f : Y ⟶ X} (hf : PreservesDenseOpens f)
    {φ ψ : PartialMap X (affineLine S)} (h : PartialMap.equiv φ ψ) :
    (φ.precomp hf).toRationalMap = (ψ.precomp hf).toRationalMap :=
  sorry

/-- Pull back rational functions along a morphism that preserves dense opens. -/
def rationalFunctionComap {X Y : AlgebraicSpace S} {f : Y ⟶ X}
    (hf : PreservesDenseOpens f) : RationalFunction X →+* RationalFunction Y := by
  let g : RationalFunction X → RationalFunction Y :=
    Quotient.lift (fun ψ : PartialMap X (affineLine S) ↦ (ψ.precomp hf).toRationalMap)
      (fun _ _ h ↦ PartialMap.precomp_toRationalMap_respects hf h)
  have laws : g 1 = 1 ∧ (∀ a b, g (a * b) = g a * g b) ∧
      g 0 = 0 ∧ (∀ a b, g (a + b) = g a + g b) := by
    sorry
  exact
    { toFun := g
      map_one' := laws.1
      map_mul' := laws.2.1
      map_zero' := laws.2.2.1
      map_add' := laws.2.2.2 }

/-- Pullback on a partial-map representative is precomposition. -/
theorem rationalFunctionComap_toRationalMap {X Y : AlgebraicSpace S} {f : Y ⟶ X}
    (hf : PreservesDenseOpens f) (φ : PartialMap X (affineLine S)) :
    rationalFunctionComap hf φ.toRationalMap = (φ.precomp hf).toRationalMap :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
