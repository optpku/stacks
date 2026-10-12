/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Reflexive
public import ReasLib.AlgebraicGeometry.Scheme.Depth
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive

/-!
# Reflexive scheme modules and stalk depth

This file relates reflexivity of a coherent scheme module to reflexivity and depth of its stalks.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped ENat

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- A coherent module on an integral locally Noetherian scheme is reflexive exactly when each
stalk is reflexive or has depth at least two. -/
theorem isReflexive_iff_stalk_isReflexive_or_moduleDepth_ge_two
    (ℱ : X.Modules) [ℱ.IsCoherent] :
    IsReflexive ℱ ↔
      ∀ x : X,
        Module.IsReflexive (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) ∨
          (2 : ℕ∞) ≤
            moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) := sorry

namespace IsReflexive

/-- Every stalk of a coherent reflexive module on an integral locally Noetherian scheme is
reflexive or has depth at least two. -/
theorem stalk_isReflexive_or_moduleDepth_ge_two
    {ℱ : X.Modules} [ℱ.IsCoherent] (hℱ : IsReflexive ℱ) (x : X) :
    Module.IsReflexive (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) ∨
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) :=
  (isReflexive_iff_stalk_isReflexive_or_moduleDepth_ge_two ℱ).1 hℱ x

/-- A coherent reflexive module has stalk depth at least two wherever the local ring has depth
at least two. -/
theorem moduleDepth_stalk_ge_two_of_ringDepth_stalk_ge_two
    (ℱ : X.Modules) [ℱ.IsCoherent] [IsReflexive ℱ] (x : X)
    (hx : (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x)) :
    (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) := sorry

/-- A coherent reflexive module on an integral locally Noetherian scheme satisfies `(S₂)` if
the scheme satisfies `(S₂)`. -/
theorem satisfiesSerreConditionS_two
    (ℱ : X.Modules) [ℱ.IsCoherent] [IsReflexive ℱ]
    (hX : X.satisfiesSerreConditionS 2) :
    satisfiesSerreConditionS ℱ 2 := sorry

end IsReflexive

/-- A coherent module on an integral locally Noetherian scheme is reflexive if each stalk is
reflexive or has depth at least two. -/
theorem isReflexive_of_stalk_isReflexive_or_moduleDepth_ge_two
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hℱ : ∀ x : X,
      Module.IsReflexive (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) ∨
        (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x)) :
    IsReflexive ℱ :=
  (isReflexive_iff_stalk_isReflexive_or_moduleDepth_ge_two ℱ).2 hℱ

end AlgebraicGeometry.Scheme.Modules
