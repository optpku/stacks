module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.StalkwiseFree
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiberRank

/-!
# Conditions characterizing finite locally free scheme modules

This leaf packages the individual predicates occurring in the finite-local-freeness criterion for
quasi-coherent modules on schemes.  The primitive stalkwise-free and fiber-rank notions remain
owned by the ringed-space and locally-ringed-space layers.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A scheme module that is both of finite presentation and flat. -/
class FinitePresentationFlat (ℱ : X.Modules) : Prop extends
    ℱ.IsFinitePresentation, ℱ.IsFlat

/-- Finite presentation and flatness canonically give finite-presentation flatness. -/
instance instFinitePresentationFlat {ℱ : X.Modules}
    [ℱ.IsFinitePresentation] [ℱ.IsFlat] : FinitePresentationFlat ℱ := sorry

/-- Finite-presentation flatness is equivalent to finite presentation together with flatness. -/
theorem finitePresentationFlat_iff (ℱ : X.Modules) :
    FinitePresentationFlat ℱ ↔ ℱ.IsFinitePresentation ∧ ℱ.IsFlat := sorry

/-- A scheme module of finite presentation with free stalks. -/
class FinitePresentationStalkwiseFree (ℱ : X.Modules) : Prop extends
    ℱ.IsFinitePresentation,
    RingedSpace.Modules.IsStalkwiseFree (X := X.toRingedSpace) ℱ

/-- Finite presentation and stalkwise freeness canonically give their combined condition. -/
instance instFinitePresentationStalkwiseFree {ℱ : X.Modules}
    [ℱ.IsFinitePresentation]
    [RingedSpace.Modules.IsStalkwiseFree (X := X.toRingedSpace) ℱ] :
    FinitePresentationStalkwiseFree ℱ := sorry

/-- The finite-presentation stalkwise-free condition is equivalent to its two constituents. -/
theorem finitePresentationStalkwiseFree_iff (ℱ : X.Modules) :
    FinitePresentationStalkwiseFree ℱ ↔
      ℱ.IsFinitePresentation ∧
        RingedSpace.Modules.IsStalkwiseFree (X := X.toRingedSpace) ℱ := sorry

/-- A scheme module that is locally free and of finite type. -/
class LocallyFreeFiniteType (ℱ : X.Modules) : Prop extends
    SheafOfModules.IsLocallyFree
      (J := Opens.grothendieckTopology X.toRingedSpace)
      (R := X.toRingedSpace.ringCatSheaf) ℱ,
    ℱ.IsFiniteType

/-- Local freeness and finite type canonically give locally-free finite type. -/
instance instLocallyFreeFiniteType {ℱ : X.Modules}
    [SheafOfModules.IsLocallyFree
      (J := Opens.grothendieckTopology X.toRingedSpace)
      (R := X.toRingedSpace.ringCatSheaf) ℱ]
    [ℱ.IsFiniteType] : LocallyFreeFiniteType ℱ := sorry

/-- The locally-free finite-type condition is equivalent to local freeness and finite type. -/
theorem locallyFreeFiniteType_iff (ℱ : X.Modules) :
    LocallyFreeFiniteType ℱ ↔
      SheafOfModules.IsLocallyFree
          (J := Opens.grothendieckTopology X.toRingedSpace)
          (R := X.toRingedSpace.ringCatSheaf) ℱ ∧
        ℱ.IsFiniteType := sorry

/-- A scheme module of finite type with free stalks and locally constant fiber rank. -/
class FiniteTypeStalkwiseFreeRankLocallyConstant (ℱ : X.Modules) : Prop extends
    ℱ.IsFiniteType,
    RingedSpace.Modules.IsStalkwiseFree (X := X.toRingedSpace) ℱ,
    IsFiberRankLocallyConstant ℱ

/-- Finite type, stalkwise freeness, and locally constant fiber rank canonically give their
combined condition. -/
instance instFiniteTypeStalkwiseFreeRankLocallyConstant {ℱ : X.Modules}
    [ℱ.IsFiniteType]
    [RingedSpace.Modules.IsStalkwiseFree (X := X.toRingedSpace) ℱ]
    [IsFiberRankLocallyConstant ℱ] :
    FiniteTypeStalkwiseFreeRankLocallyConstant ℱ := sorry

/-- The finite-type stalkwise-free locally-constant-rank condition is equivalent to its three
constituents. -/
theorem finiteTypeStalkwiseFreeRankLocallyConstant_iff (ℱ : X.Modules) :
    FiniteTypeStalkwiseFreeRankLocallyConstant ℱ ↔
      ℱ.IsFiniteType ∧
        RingedSpace.Modules.IsStalkwiseFree (X := X.toRingedSpace) ℱ ∧
          IsFiberRankLocallyConstant ℱ := sorry

end AlgebraicGeometry.Scheme.Modules
