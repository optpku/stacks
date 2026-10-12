/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Flattening
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank

/-!
# Universal flattenings

This module records the existence of a representing scheme for the flattening functor of a
quasicoherent module and for its specialization to the structure module.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

namespace Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) [ℱ.IsQuasicoherent]

/-- A quasicoherent module has a universal flattening when its flattening functor is
representable by a scheme over the base. -/
abbrev HasUniversalFlattening : Prop :=
  (Flattening.functor f ℱ).IsRepresentable

end Modules

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A scheme has a universal flattening when its structure module has a universal flattening. -/
abbrev HasUniversalFlattening : Prop :=
  Modules.HasUniversalFlattening f (SheafOfModules.unit X.ringCatSheaf : X.Modules)

end AlgebraicGeometry.Scheme
