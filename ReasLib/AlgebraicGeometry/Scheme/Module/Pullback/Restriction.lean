/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback along a restricted scheme morphism of the restriction of a module is
canonically isomorphic to the restriction of its pullback. -/
def pullbackRestrictIso {X Y : Scheme.{u}} (j : Y ⟶ X) (U : X.Opens)
    (M : X.Modules) :
    (pullback (j ∣_ U)).obj (M.restrict U.ι) ≅
      ((pullback j).obj M).restrict (j ⁻¹ᵁ U).ι :=
  (pullback (j ∣_ U)).mapIso ((restrictFunctorIsoPullback U.ι).app M) ≪≫
    (pullbackComp (j ∣_ U) U.ι).app M ≪≫
    (pullbackCongr (morphismRestrict_ι j U)).app M ≪≫
    ((pullbackComp (j ⁻¹ᵁ U).ι j).app M).symm ≪≫
    ((restrictFunctorIsoPullback (j ⁻¹ᵁ U).ι).app ((pullback j).obj M)).symm

end AlgebraicGeometry.Scheme.Modules
