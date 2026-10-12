/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.Dominance
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 37.81.3: for the canonical morphism `X.toSpecΓ`, the largest quasi-coherent ideal
sheaf contained in its kernel is zero; if `X` is quasi-compact, its structure-sheaf map is
injective and the morphism is dominant. -/
@[stacks 0H2R] #check
  (AlgebraicGeometry.IsSchemeTheoreticallyDominant.toSpecΓ :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      AlgebraicGeometry.IsSchemeTheoreticallyDominant X.toSpecΓ)

#check
  (AlgebraicGeometry.Scheme.mono_toSpecΓ_c :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [CompactSpace X],
      CategoryTheory.Mono X.toSpecΓ.c)

#check
  (AlgebraicGeometry.instIsDominantToSpecΓOfCompactSpaceCarrierCarrierCommRingCat :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X],
      AlgebraicGeometry.IsDominant X.toSpecΓ)
