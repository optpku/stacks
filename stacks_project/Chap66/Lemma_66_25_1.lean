/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_25_4_Regular

/-!
# Regularity via étale local rings

A locally Noetherian algebraic space is regular if and only if every étale local ring
at a geometric point is a regular local ring.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 66.25.1: let `S` be a scheme, and let `X` be a locally Noetherian algebraic space
over `S`. Then `X` is regular if and only if every étale local ring `etaleLocalRing X xbar`
is a regular local ring. -/
@[stacks 06LQ]
theorem isRegular_iff_forall_etaleLocalRing {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] :
    IsRegular X ↔ ∀ xbar : GeometricPoint X, IsRegularLocalRing (etaleLocalRing X xbar) :=
  sorry

/-- The étale local ring of a regular locally Noetherian algebraic space at a geometric
point is a regular local ring. -/
instance etaleLocalRing.instIsRegularLocalRing {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsRegular X] (xbar : GeometricPoint X) :
    IsRegularLocalRing (etaleLocalRing X xbar) :=
  sorry

/-- A locally Noetherian algebraic space is regular if every étale local ring at a geometric
point is a regular local ring. -/
theorem isRegular_of_forall_etaleLocalRing {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X]
    (h : ∀ xbar : GeometricPoint X, IsRegularLocalRing (etaleLocalRing X xbar)) :
    IsRegular X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
