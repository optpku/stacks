/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.FiniteFibers
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- There exists an étale morphism of algebraic spaces with two distinct specializing
points having the same image under the induced map on points. -/
@[stacks 06UK]
theorem exists_etale_nontrivial_specialization_in_fibre :
    ∃ (S : Scheme.{u}) (X Y : AlgebraicSpace S) (f : X ⟶ Y) (x x' : Points X),
      Etale f ∧ Specializes x x' ∧ x ≠ x' ∧ Points.map f x = Points.map f x' :=
  sorry

/-- Two specializing points of a scheme with an étale morphism to an algebraic
space are equal if they have the same image and that image admits an étale scheme
covering with finite fibres. -/
@[stacks 03IM]
theorem eq_of_specializes_of_existsEtaleCoverFiniteFibre {S : Scheme.{u}}
    {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]
    {u u' : U.left} {x : Points X} (hu : Points.mapOfOver φ u = x)
    (hu' : Points.mapOfOver φ u' = x) (hspec : Specializes u' u)
    (h_finiteFibre : existsEtaleCoverFiniteFibre X x) : u = u' :=
  sorry

/-- For an étale morphism from a scheme to a locally Noetherian algebraic space,
specializing points in a common fibre are equal. -/
@[stacks 0H1Q]
theorem eq_of_specializes_of_mapOfOver_eq {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsLocallyNoetherian X] {U : Over S} (φ : ofOver U ⟶ X)
    [Etale φ] {u u' : U.left} {x : Points X} (hu : Points.mapOfOver φ u = x)
    (hu' : Points.mapOfOver φ u' = x) (hspec : Specializes u' u) : u = u' :=
  sorry

/-- Two specializing points of a scheme with an étale morphism to an algebraic
space are equal if they have the same image and every affine étale scheme has
finite fibre over that image. -/
theorem eq_of_specializes_of_forallAffineEtaleFiniteFibre {S : Scheme.{u}}
    {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]
    {u u' : U.left} {x : Points X} (hu : Points.mapOfOver φ u = x)
    (hu' : Points.mapOfOver φ u' = x) (hspec : Specializes u' u)
    (h_affine : forallAffineEtaleFiniteFibre X x) : u = u' :=
  eq_of_specializes_of_existsEtaleCoverFiniteFibre φ hu hu' hspec
    ((existsEtaleCoverFiniteFibre_iff X x).mpr h_affine)

end AlgebraicGeometry.AlgebraicSpace
