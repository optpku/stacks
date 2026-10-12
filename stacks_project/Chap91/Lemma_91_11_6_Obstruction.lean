/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.Lemma_91_10_2_Obstruction
public import stacks_project.Chap91.Lemma_91_11_2_Canonical

/-!
# Relative Ext¹ obstruction of a map of modules along a strict first-order thickening

A strict morphism of first-order thickenings and an `O`-linear map `φ : i^* F' ⟶ i^* G'`
between modules flat over `O_{B'}` determine a mixed-scalar extension with kernel
`f^* J ⊗ i^* F'` and a canonical class `o(φ)` in `Ext (i^* F') (f^* J ⊗ i^* G') 1`,
obtained from the 91.10.2 difference of endpoint maps with `ψ = 1 ⊗ φ`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Abelian (Ext)
open SheafOfModules.ChangeOfRings
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {OB' OB O' O : Sheaf J CommRingCat.{max u v}}
variable (π : O' ⟶ O) {τ : OB' ⟶ OB}
variable [IsFirstOrderThickening π] [IsFirstOrderThickening τ]
variable [(restrictScalars (ringSheafMap π)).IsRightAdjoint]
variable (f : OB ⟶ O) [(restrictScalars (ringSheafMap f)).IsRightAdjoint]
variable (f' : OB' ⟶ O') (hcomm : f' ≫ π = τ ≫ f)

/-- The mixed-scalar extension `0 ⟶ f^* J ⊗ i^* F' ⟶ F' ⟶ i^* F' ⟶ 0` obtained by
reassociating `ofPullback` along `canonicalMap`, for `F'` flat over `O_{B'}` and
`(f, f')` strict. -/
def ofSourceIdealMul (F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O')
    [IsFlat OB' ((restrictionAlong f').obj F')] (hstrict : IsStrict f f' hcomm) :
    Extension π where
  kernel :=
    moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ))
      ((extendScalars (ringSheafMap π)).obj F')
  middle := F'
  quot := (extendScalars (ringSheafMap π)).obj F'
  ι := (restrictionAlong π).map (canonicalMap π f f' hcomm F') ≫
    (ofPullback π F').ι
  p := (ofPullback π F').p
  zero := sorry
  shortExact := sorry

/-- The kernel, middle, quotient, inclusion, and projection of `ofSourceIdealMul`. -/
theorem ofSourceIdealMul_spec
    (F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O')
    [IsFlat OB' ((restrictionAlong f').obj F')] (hstrict : IsStrict f f' hcomm) :
    (ofSourceIdealMul π f f' hcomm F' hstrict).kernel =
        moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ))
          ((extendScalars (ringSheafMap π)).obj F') ∧
      (ofSourceIdealMul π f f' hcomm F' hstrict).middle = F' ∧
      (ofSourceIdealMul π f f' hcomm F' hstrict).quot =
        (extendScalars (ringSheafMap π)).obj F' ∧
      (ofSourceIdealMul π f f' hcomm F' hstrict).ι =
        (restrictionAlong π).map (canonicalMap π f f' hcomm F') ≫
          (ofPullback π F').ι ∧
      (ofSourceIdealMul π f f' hcomm F' hstrict).p = (ofPullback π F').p := sorry

/-- The kernel map `ψ = 1 ⊗ φ` associated to an `O`-linear map `φ : i^* F' ⟶ i^* G'`. -/
def tensorKernelMap {F' G' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O'}
    (φ : (extendScalars (ringSheafMap π)).obj F' ⟶
      (extendScalars (ringSheafMap π)).obj G') :
    moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ))
        ((extendScalars (ringSheafMap π)).obj F') ⟶
      moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ))
        ((extendScalars (ringSheafMap π)).obj G') :=
  moduleTensorMap (𝟙 ((extendScalars (ringSheafMap f)).obj (ideal τ))) φ

/-- `tensorKernelMap π f φ` is `moduleTensorMap (𝟙 (f^* J)) φ`. -/
theorem tensorKernelMap_eq {F' G' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O'}
    (φ : (extendScalars (ringSheafMap π)).obj F' ⟶
      (extendScalars (ringSheafMap π)).obj G') :
    tensorKernelMap π f φ =
      moduleTensorMap (𝟙 ((extendScalars (ringSheafMap f)).obj (ideal τ))) φ := sorry

/-- The infinitesimal-map square of `φ` and `1 ⊗ φ` commutes for `ofSourceIdealMul`. -/
theorem tensorKernelMap_comm {F' G' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O'}
    [IsFlat OB' ((restrictionAlong f').obj F')]
    [IsFlat OB' ((restrictionAlong f').obj G')]
    (hstrict : IsStrict f f' hcomm)
    (φ : (extendScalars (ringSheafMap π)).obj F' ⟶
      (extendScalars (ringSheafMap π)).obj G') :
    infMapCommSq (ofSourceIdealMul π f f' hcomm F' hstrict)
      (ofSourceIdealMul π f f' hcomm G' hstrict) φ (tensorKernelMap π f φ) := sorry

variable [HasExt (ringedSiteModuleCategory.{u, v, max u v, max u v} J O)]

/-- The obstruction class `o(φ) ∈ Ext (i^* F') (f^* J ⊗ i^* G') 1` of an `O`-linear
map along a strict morphism of first-order thickenings, for modules flat over `O_{B'}`. -/
noncomputable def obstruction {F' G' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O'}
    [IsFlat OB' ((restrictionAlong f').obj F')]
    [IsFlat OB' ((restrictionAlong f').obj G')]
    (hstrict : IsStrict f f' hcomm)
    (φ : (extendScalars (ringSheafMap π)).obj F' ⟶
      (extendScalars (ringSheafMap π)).obj G') :
    Ext ((extendScalars (ringSheafMap π)).obj F')
      (moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ))
        ((extendScalars (ringSheafMap π)).obj G')) 1 :=
  mapObstruction (ofSourceIdealMul π f f' hcomm F' hstrict)
    (ofSourceIdealMul π f f' hcomm G' hstrict) φ (tensorKernelMap π f φ)
    (tensorKernelMap_comm π f f' hcomm hstrict φ)

/-- `obstruction π f f' hcomm hstrict φ` is the 91.10.2 class `o(φ, 1 ⊗ φ)` of
`ofSourceIdealMul`. -/
theorem obstruction_eq {F' G' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O'}
    [IsFlat OB' ((restrictionAlong f').obj F')]
    [IsFlat OB' ((restrictionAlong f').obj G')]
    (hstrict : IsStrict f f' hcomm)
    (φ : (extendScalars (ringSheafMap π)).obj F' ⟶
      (extendScalars (ringSheafMap π)).obj G') :
    obstruction π f f' hcomm hstrict φ =
      mapObstruction (ofSourceIdealMul π f f' hcomm F' hstrict)
        (ofSourceIdealMul π f f' hcomm G' hstrict) φ (tensorKernelMap π f φ)
        (tensorKernelMap_comm π f f' hcomm hstrict φ) := sorry

end SheafOfModules.RingedSite.FirstOrderThickening
