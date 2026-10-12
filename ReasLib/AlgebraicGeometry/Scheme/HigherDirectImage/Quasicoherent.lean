/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiSeparated

/-!
# Quasicoherence of Higher Direct Images

This module records preservation of quasicoherence by higher direct images along
quasi-compact and quasi-separated morphisms of schemes.
-/

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}}

/-- Every higher direct image of a quasi-coherent module along a quasi-compact and
quasi-separated morphism of schemes is quasi-coherent. -/
@[stacks 01XJ, instance]
theorem higherDirectImageModule_isQuasicoherent_of_quasiCompact_quasiSeparated
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (p : ℕ) :
    (higherDirectImageModule f.toShHom ℱ p).IsQuasicoherent := sorry

end AlgebraicGeometry.Scheme
