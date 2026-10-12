/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.Properties
import StacksCheckRecall

/-!
# Lemma 29.45.5 compatibility entry point

The characterization of universal homeomorphisms is owned by the neutral
scheme-morphism API in `ReasLib`.
-/

@[expose] public section

universe u

/- Lemma 29.45.5 (Stacks 04DF): a scheme morphism is a universal
homeomorphism exactly when it is integral, universally injective, and
surjective. -/
@[stacks 04DF] #check
  (@AlgebraicGeometry.UniversalHomeomorphism.iff_isIntegralHom_and_universallyInjective_and_surjective :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
      AlgebraicGeometry.UniversalHomeomorphism f ↔
        AlgebraicGeometry.IsIntegralHom f ∧
          AlgebraicGeometry.UniversallyInjective f ∧ AlgebraicGeometry.Surjective f)
