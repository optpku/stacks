/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Trivial universe lifts in `ModuleCat`

The category-level `ULift` functor is fully faithful, but a lift whose target universe is already
the source universe is not definitionally the identity.  This leaf records the canonical natural
isomorphism removing that redundant lift.  Downstream functors obtain their comparison by left
whiskering this owner.
-/

@[expose] public section

noncomputable section

universe uR v w

open CategoryTheory

namespace ModuleCat

variable {R : Type uR} [Ring R]

/-- Naturality of the canonical equivalence removing a redundant `ModuleCat` universe lift. -/
@[reassoc, stacks 0G1X "naturality of the canonical ModuleCat lift equivalence"]
theorem uliftFunctorTrivial_naturality
    {X Y : ModuleCat.{max v w} R} (f : X ⟶ Y) :
    (ModuleCat.uliftFunctor.{w, max v w} R).map f ≫
        (ULift.moduleEquiv (R := R) (M := (Y : Type (max v w)))).toModuleIso.hom =
      (ULift.moduleEquiv (R := R) (M := (X : Type (max v w)))).toModuleIso.hom ≫ f := by
  ext x
  rfl

/-- The `ModuleCat` universe lift is canonically isomorphic to the identity whenever its source
universe already contains the requested lift universe. -/
@[stacks 0G1X "canonical triviality of a redundant ModuleCat universe lift"]
def uliftFunctorTrivial :
    ModuleCat.uliftFunctor.{w, max v w} R ≅ 𝟭 (ModuleCat.{max v w} R) :=
  NatIso.ofComponents
    (fun X ↦
      (ULift.moduleEquiv (R := R) (M := (X : Type (max v w)))).toModuleIso)
    (fun f ↦ uliftFunctorTrivial_naturality f)

/-- The component of `uliftFunctorTrivial` is the canonical `ULift.moduleEquiv`. -/
@[simp, stacks 0G1X "component of the canonical trivial ModuleCat lift"]
theorem uliftFunctorTrivial_app (X : ModuleCat.{max v w} R) :
    (uliftFunctorTrivial.{uR, v, w} (R := R)).app X =
      (ULift.moduleEquiv (R := R) (M := (X : Type (max v w)))).toModuleIso := by
  rfl

end ModuleCat
