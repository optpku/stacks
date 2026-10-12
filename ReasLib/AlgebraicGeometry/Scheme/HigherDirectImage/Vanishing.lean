/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.TopDegreeBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension

/-!
# Vanishing of Higher Direct Images

This module records uniform upper bounds for higher direct images along quasi-compact and
quasi-separated morphisms, together with vanishing above the dimension of a fiber of a proper
morphism.
-/

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X S Y : Scheme.{u}}

namespace HigherDirectImage

/-- Over a quasi-compact base, the higher direct images along every base change of a
quasi-compact and quasi-separated morphism vanish above one uniform degree. -/
@[stacks 01XJ]
theorem eventually_isZero_after_baseChange
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [CompactSpace S.carrier] :
    ∃ n : ℕ, ∀ ⦃S' : Scheme.{u}⦄ (g : S' ⟶ S)
      (ℱ' : (pullback f g : Scheme.{u}).Modules), ℱ'.IsQuasicoherent → ∀ p : ℕ, n ≤ p →
      IsZero (higherDirectImageModule (pullback.snd f g).toShHom ℱ' p) := sorry

/-- If a proper morphism has a fiber of dimension `d` at `y`, then some affine open
neighborhood of `y` has vanishing higher direct images above degree `d`, uniformly for all
quasicoherent modules on the restricted source. -/
@[stacks 0E7D]
theorem exists_affineOpen_isZero_above_of_proper_of_fiberDimension_eq
    (f : X ⟶ Y) [IsProper f] (y : Y) (d : ℕ)
    (hdim : topologicalKrullDim (f.fiber y) = (d : WithBot ℕ∞)) :
    ∃ (V : Y.Opens) (_ : IsAffineOpen V) (_ : y ∈ V),
      ∀ (ℱ : (f ⁻¹ᵁ V).toScheme.Modules) [ℱ.IsQuasicoherent] (i : ℕ), d < i →
        IsZero (RingedSpace.Hom.higherDirectImageModule (f ∣_ V).toShHom ℱ i) := sorry

/-- If a proper morphism has a fiber of dimension `d` at `y`, then on some affine open
neighborhood of `y` its restriction satisfies the complete top-degree base-change property in
degree `d`. -/
@[stacks 0E7D]
theorem exists_affineOpen_topDegreeBaseChange_of_proper_of_fiberDimension_eq
    (f : X ⟶ Y) [IsProper f] (y : Y) (d : ℕ)
    (hdim : topologicalKrullDim (f.fiber y) = (d : WithBot ℕ∞)) :
    ∃ (V : Y.Opens) (_ : IsAffineOpen V) (_ : y ∈ V),
      TopDegreeBaseChange (f ∣_ V) d := sorry

/-- If a proper morphism has a fiber of dimension `d` at `y`, then the stalk at `y` of every
quasicoherent higher direct image above degree `d` is zero. -/
@[stacks 0E7D]
theorem stalk_isZero_of_proper_of_fiberDimension_eq
    (f : X ⟶ Y) [IsProper f] (y : Y) (d : ℕ)
    (hdim : topologicalKrullDim (f.fiber y) = (d : WithBot ℕ∞))
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℕ) (hi : d < i) :
    IsZero
      (RingedSpace.stalkModuleCat
        (RingedSpace.Hom.higherDirectImageModule f.toShHom ℱ i) y) := sorry

variable {X' Y' : Scheme.{u}}

/-- For a proper morphism with a fiber of dimension at most one, vanishing of the first
higher direct image of the structure sheaf after a cartesian base change through a point over
the given point implies vanishing of the first cohomology of the original fiber. -/
@[stacks 0E7F]
theorem fiberH1_isZero_of_baseChange
    (f : X ⟶ Y) [IsProper f] (y : Y)
    (hdim : topologicalKrullDim (f.fiber y) ≤ (1 : WithBot ℕ∞))
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    (hcart : IsPullback g' f' f g) (y' : Y') (hy : g y' = y)
    (hR1 : IsZero
      (RingedSpace.Hom.higherDirectImageModule f'.toShHom
        (SheafOfModules.unit X'.ringCatSheaf) 1)) :
    IsZero
      (Scheme.Modules.cohomology
        (SheafOfModules.unit (f.fiber y).ringCatSheaf) 1) := sorry

/-- Vanishing of the first higher direct image of the structure sheaf along a proper morphism
implies vanishing of the first cohomology of each fiber of dimension at most one. -/
theorem fiberH1_isZero_of_degreeOne_isZero
    (f : X ⟶ Y) [IsProper f] (y : Y)
    (hdim : topologicalKrullDim (f.fiber y) ≤ (1 : WithBot ℕ∞))
    (hR1 : IsZero
      (RingedSpace.Hom.higherDirectImageModule f.toShHom
        (SheafOfModules.unit X.ringCatSheaf) 1)) :
    IsZero
      (Scheme.Modules.cohomology
        (SheafOfModules.unit (f.fiber y).ringCatSheaf) 1) := sorry

/-- If the fiber of a proper morphism over a point has dimension at most one and vanishing
first cohomology of its structure sheaf, then the first higher direct image of the structure
sheaf vanishes on an open neighborhood of the point, also after every base change. -/
@[stacks 0E7G]
theorem exists_open_structureSheaf_degreeOne_isZero
    (f : X ⟶ Y) [IsProper f] (y : Y)
    (hdim : topologicalKrullDim (f.fiber y) ≤ (1 : WithBot ℕ∞))
    (hH1 : IsZero
      (Scheme.Modules.cohomology (SheafOfModules.unit (f.fiber y).ringCatSheaf) 1)) :
    ∃ V : Y.Opens, y ∈ V ∧
      IsZero
        ((RingedSpace.Hom.higherDirectImageModule f.toShHom
          (SheafOfModules.unit X.ringCatSheaf) 1).over V) ∧
      ∀ {X' Y' : Scheme.{u}}
        (g' : X' ⟶ (f ⁻¹ᵁ V).toScheme) (f' : X' ⟶ Y') (g : Y' ⟶ V),
        IsPullback g' f' (f ∣_ V) g →
          IsZero
            (RingedSpace.Hom.higherDirectImageModule f'.toShHom
              (SheafOfModules.unit X'.ringCatSheaf) 1) := sorry

end HigherDirectImage

/-- Over a quasi-compact base, the higher direct images of quasi-coherent modules along a
quasi-compact and quasi-separated morphism vanish above one degree. -/
@[stacks 01XJ]
theorem eventually_higherDirectImageModule_isZero_of_quasiCompact_base
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [CompactSpace S.carrier] :
    ∃ n : ℕ, ∀ (ℱ : X.Modules), ℱ.IsQuasicoherent → ∀ p : ℕ, n ≤ p →
      IsZero (higherDirectImageModule f.toShHom ℱ p) := sorry

end AlgebraicGeometry.Scheme
