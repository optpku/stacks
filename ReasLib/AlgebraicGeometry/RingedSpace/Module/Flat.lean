/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Flatness for module sheaves on ringed spaces

This file provides the shared-library definitions and characterizations of flatness for sheaves
of modules on a ringed space:

- `SheafOfModules.IsFlatAt`: pointwise flatness at a single point
- `SheafOfModules.IsFlat`: the class asserting flatness at all points
- `SheafOfModules.IsFlat.iff_forall_isFlatAt`: the stalkwise characterization
- `SheafOfModules.unit_isFlat`: the structure sheaf is flat
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}

/-- An `𝒪_X`-module `ℱ` is flat at `x` if its stalk `ℱ_x` is a flat module over `𝒪_{X,x}`. -/
@[stacks 05NF]
abbrev IsFlatAt (ℱ : RingedSpace.Modules X) (x : X) : Prop :=
  Module.Flat (X.presheaf.stalk x) (stalkModuleCat ℱ x)

/-- An `𝒪_X`-module is flat if it is flat at every point. -/
@[stacks 05ND]
class IsFlat (ℱ : RingedSpace.Modules X) : Prop where
  flatAt (x : X) : ℱ.IsFlatAt x

/-- Flatness of a module sheaf is equivalent to flatness at every point. -/
@[stacks 05NE]
theorem IsFlat.iff_forall_isFlatAt (ℱ : RingedSpace.Modules X) :
    ℱ.IsFlat ↔ ∀ x : X, ℱ.IsFlatAt x := sorry

/-- A flat module sheaf is flat at every point, available directly to typeclass search. -/
instance IsFlat.atPoint {ℱ : RingedSpace.Modules X} [ℱ.IsFlat] (x : X) :
    ℱ.IsFlatAt x := sorry

/-- Pointwise flatness at every stalk constructs flatness of the module sheaf. -/
theorem IsFlat.of_forall_isFlatAt (ℱ : RingedSpace.Modules X)
    (hℱ : ∀ x : X, ℱ.IsFlatAt x) : ℱ.IsFlat := sorry

/-- Stalkwise flatness agrees with monoidal flatness on the canonical opens site. -/
@[stacks 05VC "ringed-space specialization"]
theorem isFlat_iff_ringedSite_isFlat
    (ℱ : X.Modules) :
    ℱ.IsFlat ↔
      RingedSite.IsFlat (J := Opens.grothendieckTopology (X : TopCat))
        X.sheaf ℱ := sorry

/-- Stalkwise flatness supplies the canonical monoidal flatness instance on the opens site.
This bridge lets generic ringed-site APIs consume geometric flatness hypotheses directly. -/
@[stacks 05VC "stalkwise flatness to ringed-site flatness", instance]
theorem IsFlat.ringedSite (ℱ : X.Modules) [ℱ.IsFlat] :
    RingedSite.IsFlat (J := Opens.grothendieckTopology (X : TopCat))
      X.sheaf ℱ := sorry

/-- The structure sheaf is flat. -/
instance unit_isFlat : IsFlat (unit (ringCatSheaf X)) := sorry


end SheafOfModules
