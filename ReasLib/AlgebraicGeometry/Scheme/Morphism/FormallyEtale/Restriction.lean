/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyEtale

/-!
# Restrictions of formally étale morphisms

Formally étale scheme morphisms remain formally étale after restriction to compatible
open subschemes of their source and target.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FormallyEtale

/-- Formally étale scheme morphisms remain formally étale after restriction to open
subschemes of their source and target. -/
instance resLE {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) (V : S.Opens)
    (e : U ≤ f ⁻¹ᵁ V) [FormallyEtale f] : FormallyEtale (f.resLE V U e) := sorry

end AlgebraicGeometry.FormallyEtale
