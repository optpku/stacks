/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.CommRing.Pullback

/-!
# Flat modules and flat morphisms of ringed sites

This module owns categorical flatness of ringed-site morphisms, its exact
pullback API, and the bridge to flatness of the inverse-image structure map
for commutative presentations.  The same-site tensor-flatness owner is
`ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe uX vX uY vY w z

namespace RingedSite.Hom

section

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}

/-- A morphism of ringed sites is categorically flat when its
canonical pullback on module sheaves is exact.  For commutative presentations,
`isFlat_iff_isFlatHom` identifies this with flatness of the inverse-image structure map. -/
@[stacks 04JB "categorical form"]
class IsFlat.{zFlat, u₁, v₁, u₂, v₂, wFlat}
    {X : RingedSite.{u₁, v₁, wFlat}} {Y : RingedSite.{u₂, v₂, wFlat}}
    (f : X.Hom Y) [(f.modulePushforward.{zFlat}).IsRightAdjoint] : Prop where
  /-- The canonical pullback on module sheaves is exact. -/
  exact_pullback :
    exactFunctor
      (ModuleCat.{zFlat} Y) (ModuleCat.{zFlat} X)
      f.modulePullback.{zFlat}

/-- Flat pullback, bundled with the exactness certificate carried by `IsFlat` itself.

Using this owner keeps the exactness witness attached to the functor data and avoids rebuilding
finite-limit and finite-colimit instances in downstream derived-category constructions. -/
@[stacks 0735 "flat pullback on the derived category"]
noncomputable def IsFlat.exactPullback.{zPull, uXP, vXP, uYP, vYP, wPull}
    {X : RingedSite.{uXP, vXP, wPull}} {Y : RingedSite.{uYP, vYP, wPull}}
    (f : X.Hom Y) [(f.modulePushforward.{zPull}).IsRightAdjoint] [IsFlat.{zPull} f] :
    ModuleCat.{zPull} Y ⥤ₑ ModuleCat.{zPull} X :=
  ⟨f.modulePullback.{zPull}, (inferInstance : IsFlat.{zPull} f).exact_pullback⟩

/-- Flat module pullback preserves finite limits, using the certificate stored in `IsFlat`. -/
@[stacks 0735 "flat pullback preserves finite limits"]
noncomputable def IsFlat.preservesFiniteLimits (f : X.Hom Y)
    [(f.modulePushforward.{z}).IsRightAdjoint] [IsFlat.{z} f] :
    PreservesFiniteLimits f.modulePullback.{z} :=
  (inferInstance : IsFlat.{z} f).exact_pullback.1

/-- Flat module pullback preserves finite colimits, using the certificate stored in `IsFlat`. -/
@[stacks 0735 "flat pullback preserves finite colimits"]
noncomputable def IsFlat.preservesFiniteColimits (f : X.Hom Y)
    [(f.modulePushforward.{z}).IsRightAdjoint] [IsFlat.{z} f] :
    PreservesFiniteColimits f.modulePullback.{z} :=
  (inferInstance : IsFlat.{z} f).exact_pullback.2

/-- A flat ringed-site morphism has exact module pullback. -/
@[stacks 04JC "(2)"]
theorem IsFlat.pullback_exact (f : X.Hom Y)
    [(f.modulePushforward.{z}).IsRightAdjoint] [IsFlat.{z} f] :
    exactFunctor
      (ModuleCat.{z} Y) (ModuleCat.{z} X)
      f.modulePullback.{z} := sorry

end

end RingedSite.Hom

namespace RingedSite.Hom

section CommPresentations

variable {C : Type uX} [Category.{vX} C] {D : Type uY} [Category.{vY} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify JC AddCommGrpCat.{w}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {𝒪 : Sheaf JC CommRingCat.{w}}
variable {𝒪' : Sheaf JD CommRingCat.{w}}

/-- In a commutative presentation, categorical flatness of a
ringed-site morphism is equivalently
expressed by flatness of the inverse-image structure-sheaf map `f^♯`. -/
@[stacks 04JB "structure-map criterion"]
theorem isFlat_iff_isFlatHom
    (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JC 𝒪)
      (RingedSite.ofCommRingSheaf JD 𝒪'))
    [h_comm :
      (f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    [h_mod : f.modulePushforward.{w}.IsRightAdjoint] :
    RingedSite.Hom.IsFlat.{w} f ↔
      SheafOfModules.RingedSite.IsFlatHom (inverseImageStructureSheafMap f) := sorry

end CommPresentations

end RingedSite.Hom

namespace SheafOfModules.RingedSite

section FlatOver

variable {C : Type uX} [Category.{vX} C] {D : Type uY} [Category.{vY} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify JC AddCommGrpCat.{w}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {𝒪 : Sheaf JC CommRingCat.{w}}
variable {𝒪' : Sheaf JD CommRingCat.{w}}

/-- An `𝒪`-module is flat over the target of `f` when its
restriction along the inverse-image structure map is flat over `f⁻¹𝒪'`. -/
@[stacks 08M5]
abbrev IsFlatOver
    (M : ringedSiteModuleCategory JC 𝒪)
    (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JC 𝒪)
      (RingedSite.ofCommRingSheaf JD 𝒪'))
    [h_adj :
      (f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint] : Prop :=
  IsFlat (RingedSite.Hom.inverseImageStructureSheaf f)
    ((restrictionAlong (RingedSite.Hom.inverseImageStructureSheafMap f)).obj M)

/-- Pullback along a morphism of ringed sites followed by tensoring with a module on the
source.  This is the functor whose exactness is characterized by relative flatness. -/
@[stacks 0GMU "ringed-site pullback-tensor functor"]
noncomputable abbrev pullbackTensor
    (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JC 𝒪)
      (RingedSite.ofCommRingSheaf JD 𝒪'))
    (M : ringedSiteModuleCategory JC 𝒪)
    [h_mod : f.modulePushforward.{w}.IsRightAdjoint] :
    CategoryTheory.Functor (ringedSiteModuleCategory JD 𝒪')
      (ringedSiteModuleCategory JC 𝒪) :=
  f.modulePullback.{w} ⋙ CategoryTheory.MonoidalCategory.tensorRight M

namespace IsFlatOver

/-- Relative flatness makes pullback followed by tensoring exact. -/
@[stacks 0GMU "ringed-site form"]
theorem pullbackTensorExact
    (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JC 𝒪)
      (RingedSite.ofCommRingSheaf JD 𝒪'))
    (M : ringedSiteModuleCategory JC 𝒪)
    [h_adj :
      (f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    [h_mod : f.modulePushforward.{w}.IsRightAdjoint]
    [IsFlatOver M f] :
    exactFunctor (ringedSiteModuleCategory JD 𝒪')
      (ringedSiteModuleCategory JC 𝒪) (pullbackTensor f M) := sorry

/-- A relatively flat pullback-tensor functor preserves finite limits. -/
@[stacks 0GMU "ringed-site finite-limit preservation"]
noncomputable def pullbackTensorPreservesFiniteLimits
    (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JC 𝒪)
      (RingedSite.ofCommRingSheaf JD 𝒪'))
    (M : ringedSiteModuleCategory JC 𝒪)
    [h_adj :
      (f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    [h_mod : f.modulePushforward.{w}.IsRightAdjoint]
    [IsFlatOver M f] :
    PreservesFiniteLimits (pullbackTensor f M) :=
  (pullbackTensorExact f M).1

/-- A relatively flat pullback-tensor functor preserves finite colimits. -/
@[stacks 0GMU "ringed-site finite-colimit preservation"]
noncomputable def pullbackTensorPreservesFiniteColimits
    (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JC 𝒪)
      (RingedSite.ofCommRingSheaf JD 𝒪'))
    (M : ringedSiteModuleCategory JC 𝒪)
    [h_adj :
      (f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    [h_mod : f.modulePushforward.{w}.IsRightAdjoint]
    [IsFlatOver M f] :
    PreservesFiniteColimits (pullbackTensor f M) :=
  (pullbackTensorExact f M).2

/-- Pullback followed by tensoring with a relatively flat module, bundled as an exact
functor. -/
@[stacks 0GMU "bundled ringed-site exact functor"]
noncomputable abbrev exactPullbackTensor
    (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JC 𝒪)
      (RingedSite.ofCommRingSheaf JD 𝒪'))
    (M : ringedSiteModuleCategory JC 𝒪)
    [h_adj :
      (f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    [h_mod : f.modulePushforward.{w}.IsRightAdjoint]
    [IsFlatOver M f] :
    CategoryTheory.ExactFunctor (ringedSiteModuleCategory JD 𝒪')
      (ringedSiteModuleCategory JC 𝒪) :=
  ⟨pullbackTensor f M, pullbackTensorExact f M⟩

end IsFlatOver

end FlatOver

end SheafOfModules.RingedSite
