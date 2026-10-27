/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Flat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite

/-!
# Relative flatness of module sheaves on ringed spaces

This file owns the change-of-scalars module underlying relative flatness. It separates the
canonical restricted module from its target-stalk description, so results about either layer can
be used for arbitrary morphisms of ringed spaces.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open CategoryTheory
open SheafOfModules.RingedSite (restrictionAlong)

noncomputable section

universe u

namespace SheafOfModules

variable {X Y : RingedSpace.{u}}

/-- An `X`-module viewed by restriction of scalars along the
inverse-image structure-sheaf map of `f : X ⟶ Y`. -/
@[stacks 08KT "restricted module"]
abbrev relativeModule
    (ℱ : X.Modules) (f : X ⟶ Y) :
    RingedSpace.Modules
      { carrier := X
        presheaf := ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj Y.sheaf).presheaf
        IsSheaf := ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj Y.sheaf).2 } :=
  (restrictionAlong (RingedSpace.Hom.inverseImageStructureSheafHomComm f)).obj ℱ

/-- The stalk of `relativeModule ℱ f`, transported to a module over
the target local ring `𝒪_{Y,f(x)}`. -/
@[stacks 08KT "target-stalk module"]
abbrev targetStalkModule
    (ℱ : X.Modules) (f : X ⟶ Y) (x : X) :
    ModuleCat (Y.presheaf.stalk (f.hom.base x)) :=
  (ModuleCat.restrictScalars (f.hom.stalkMap x).hom).obj
    (stalkModuleCat ℱ x)

/-- `ℱ` is flat over `Y` at `x` when its transported stalk is flat
over the local ring `𝒪_{Y,f(x)}`. -/
@[stacks 08KT "(1)"]
abbrev IsFlatOverAt
    (ℱ : X.Modules) (f : X ⟶ Y) (x : X) : Prop :=
  Module.Flat (Y.presheaf.stalk (f.hom.base x)) (targetStalkModule ℱ f x)

/-- Compatibility spelling for pointwise relative flatness.  New APIs use
`IsFlatOverAt`. -/
abbrev flatOverAt
    (ℱ : X.Modules) (f : X ⟶ Y) (x : X) : Prop :=
  IsFlatOverAt ℱ f x

/-- `ℱ` is flat over `Y` when its canonical
`f⁻¹𝒪_Y`-module is flat. -/
@[stacks 08KT "(2)"]
abbrev IsFlatOver
    (ℱ : X.Modules) (f : X ⟶ Y) : Prop :=
  (relativeModule ℱ f).IsFlat

/-- Compatibility spelling for relative flatness.  New APIs use `IsFlatOver`. -/
abbrev flatOver
    (ℱ : X.Modules) (f : X ⟶ Y) : Prop :=
  IsFlatOver ℱ f

/-- The target-stalk formulation of relative flatness agrees with ordinary flatness of the
restricted module sheaf. -/
@[stacks 08KT "pointwise comparison"]
theorem isFlatOverAt_iff_relativeModule_isFlatAt
    (ℱ : X.Modules) (f : X ⟶ Y) (x : X) :
    IsFlatOverAt ℱ f x ↔ (relativeModule ℱ f).IsFlatAt x := sorry

/-- Compatibility form of `isFlatOverAt_iff_relativeModule_isFlatAt`. -/
theorem flatOverAt_iff_relativeModule_isFlatAt
    (ℱ : X.Modules) (f : X ⟶ Y) (x : X) :
    flatOverAt ℱ f x ↔ (relativeModule ℱ f).IsFlatAt x := sorry

/-- Relative flatness is equivalent to flatness at every source point over the corresponding
target local ring. -/
@[stacks 08KT "stalkwise comparison"]
theorem isFlatOver_iff_forall_isFlatOverAt
    (ℱ : X.Modules) (f : X ⟶ Y) :
    IsFlatOver ℱ f ↔ ∀ x : X, IsFlatOverAt ℱ f x := sorry

/-- Compatibility form of `isFlatOver_iff_forall_isFlatOverAt`. -/
theorem flatOver_iff_forall_flatOverAt
    (ℱ : X.Modules) (f : X ⟶ Y) :
    flatOver ℱ f ↔ ∀ x : X, flatOverAt ℱ f x := sorry

/-- The ringed-space relative-flatness predicate agrees with the generic opens-ringed-site
predicate. -/
@[stacks 08KT "opens-ringed-site comparison"]
theorem isFlatOver_iff_ringedSite
    (ℱ : X.Modules) (f : X ⟶ Y) :
    IsFlatOver ℱ f ↔
      RingedSite.IsFlatOver.{u, u, u, u, u} ℱ
        (RingedSpace.opensRingedSiteHom f)
        (h_adj := RingedSpace.opensRingedSiteHom.commRingPushforward_isRightAdjoint f) := sorry

namespace IsFlatOver

/-- A relatively flat module is relatively flat at every source point, available to typeclass
search. -/
@[stacks 08KT "pointwise instance"]
instance atPoint {ℱ : X.Modules} {f : X ⟶ Y} [IsFlatOver ℱ f]
    (x : X) : IsFlatOverAt ℱ f x := sorry

/-- Pointwise relative flatness at every source point constructs global relative flatness. -/
@[stacks 08KT "stalkwise constructor"]
theorem of_forall_isFlatOverAt
    (ℱ : X.Modules) (f : X ⟶ Y)
    (hℱ : ∀ x : X, IsFlatOverAt ℱ f x) : IsFlatOver ℱ f := sorry

/-- Relative flatness on a ringed space implies relative flatness on its opens ringed site. -/
@[stacks 08KT "opens-ringed-site instance"]
theorem ringedSite
    (ℱ : X.Modules) (f : X ⟶ Y) [IsFlatOver ℱ f] :
    RingedSite.IsFlatOver.{u, u, u, u, u} ℱ
      (RingedSpace.opensRingedSiteHom (X := X) (Y := Y) f)
      (h_adj := RingedSpace.opensRingedSiteHom.commRingPushforward_isRightAdjoint f) := sorry

end IsFlatOver

/-- Pullback along `f` followed by tensoring with `ℱ`. -/
@[stacks 0GMU "ringed-space pullback-tensor functor"]
noncomputable abbrev pullbackTensor
    (f : X ⟶ Y) (ℱ : X.Modules) :
    CategoryTheory.Functor Y.Modules X.Modules :=
  RingedSpace.Hom.pullback f ⋙
    CategoryTheory.MonoidalCategory.tensorRight ℱ

namespace IsFlatOver

/-- Pullback followed by tensoring with a relatively flat module is exact. -/
@[stacks 0GMU "canonical ringed-space form"]
theorem pullbackTensorExact
    (f : X ⟶ Y) (ℱ : X.Modules) [IsFlatOver ℱ f] :
    CategoryTheory.exactFunctor Y.Modules X.Modules
      (pullbackTensor f ℱ) := sorry

/-- A relatively flat pullback-tensor functor preserves finite limits. -/
@[stacks 0GMU "ringed-space finite-limit instance"]
noncomputable instance pullbackTensorPreservesFiniteLimits
    (f : X ⟶ Y) (ℱ : X.Modules) [IsFlatOver ℱ f] :
    CategoryTheory.Limits.PreservesFiniteLimits (pullbackTensor f ℱ) := sorry

/-- A relatively flat pullback-tensor functor preserves finite colimits. -/
@[stacks 0GMU "ringed-space finite-colimit instance"]
noncomputable instance pullbackTensorPreservesFiniteColimits
    (f : X ⟶ Y) (ℱ : X.Modules) [IsFlatOver ℱ f] :
    CategoryTheory.Limits.PreservesFiniteColimits (pullbackTensor f ℱ) := sorry

/-- Pullback followed by tensoring with a relatively flat module, bundled as an exact
functor. -/
@[stacks 0GMU "bundled ringed-space exact functor"]
noncomputable abbrev exactPullbackTensor
    (f : X ⟶ Y) (ℱ : X.Modules) [IsFlatOver ℱ f] :
    CategoryTheory.ExactFunctor Y.Modules X.Modules :=
  CategoryTheory.ExactFunctor.of (pullbackTensor f ℱ)

end IsFlatOver

/-- Pullback followed by tensoring with a module flat over the target is
an exact functor. -/
@[stacks 0GMU]
theorem pullback_tensor_exact_of_flatOver
    (f : X ⟶ Y) (ℱ : X.Modules) (hℱ : flatOver ℱ f) :
    CategoryTheory.exactFunctor Y.Modules X.Modules
      (pullbackTensor f ℱ) := sorry



end SheafOfModules
