/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Basic

/-!
# Base change of morphisms of scheme modules

This module defines the morphism obtained by pulling a morphism of quasicoherent scheme
modules back along a scheme base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S X : Scheme.{u}} (f : X ⟶ S)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]

/-- The morphism of modules obtained by pulling a module morphism back to `X ×_S T`. -/
def baseChangeMap {T : Scheme.{u}} (g : T ⟶ S) (u : ℱ ⟶ 𝒢) :
    baseChangeModule f g ℱ ⟶ baseChangeModule f g 𝒢 :=
  (pullback (Limits.pullback.fst f g)).map u

/-- An isomorphism after one base change remains an isomorphism after a further base change. -/
theorem baseChangeMap_isIso_of_over {T T' : Over S} (u : ℱ ⟶ 𝒢) (a : T' ⟶ T)
    (h : IsIso (baseChangeMap f T.hom u)) :
    IsIso (baseChangeMap f T'.hom u) := sorry

end AlgebraicGeometry.Scheme.Modules
