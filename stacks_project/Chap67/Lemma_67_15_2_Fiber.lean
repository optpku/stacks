/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import stacks_project.Chap66.Lemma_66_29_4_Stalk

/-!
# Residue-field fibers of étale module stalks

The étale local ring of an algebraic space at a geometric point is a local ring, and the
residue-field fiber of an `𝒪_X`-module is the tensor product of that residue field with the
étale module stalk.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The étale local ring of an algebraic space at a geometric point is a local ring. -/
instance etaleLocalRing.instIsLocalRingAtGeometricPoint {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) : IsLocalRing (etaleLocalRing X xbar) :=
  sorry

namespace Modules

/-- The residue-field fiber `κ(xbar) ⊗[𝒪_{X, xbar}] F_xbar` of an `𝒪_X`-module at a geometric
point. -/
abbrev fiber {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X)
    (F : X.Modules) : Type u :=
  IsLocalRing.ResidueField (etaleLocalRing X xbar) ⊗[etaleLocalRing X xbar]
    (stalkModuleCat xbar F)

/-- The residue-field fiber is the tensor product of the residue field of the étale local ring
with the étale module stalk. -/
theorem fiber_def {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X)
    (F : X.Modules) :
    fiber xbar F =
      IsLocalRing.ResidueField (etaleLocalRing X xbar) ⊗[etaleLocalRing X xbar]
        (stalkModuleCat xbar F) :=
  sorry

end Modules

end AlgebraicGeometry.AlgebraicSpace

