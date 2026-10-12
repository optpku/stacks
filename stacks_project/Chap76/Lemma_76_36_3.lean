/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Connected.Basic
public import stacks_project.Chap66.Definition_66_18_1_Site
public import stacks_project.Chap66.Definition_66_19_1_GeometricPoint
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap68.Lemma_68_18_6_Fibre
public import stacks_project.Chap71.Lemma_71_4_1_Fiber

/-!
# Connectedness of geometric fibres via étale scheme neighbourhoods

The geometric fibre of a morphism of algebraic spaces over a geometric point is
connected if and only if every étale scheme neighbourhood of that point has
connected residue-field fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.36.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Let `ybar` be a geometric point of `Y`. Then the geometric fibre
`fieldFiber f ybar.toFieldValuedPoint` is connected if and only if for every étale
neighbourhood `(V, vbar) ⟶ (Y, ybar)` with `V` a scheme, the residue-field fibre
`residueFiberOver f U.hom vbar.toScheme.image` of the base change is connected. -/
@[stacks 0A1A]
theorem connectedSpace_geometricFiber_iff_etaleNeighborhood
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ybar : GeometricPoint Y) :
    ConnectedSpace (Points (fieldFiber f ybar.toFieldValuedPoint)) ↔
      ∀ (U : smallEtaleSite Y) (vbar : GeometricPoint (ofOver U.left)),
        vbar.map U.hom = ybar →
          ConnectedSpace (Points (residueFiberOver f U.hom vbar.toScheme.image)) :=
  sorry

/-- Connectedness of a geometric fibre implies connectedness of the residue-field
fibre of every étale scheme neighbourhood of that geometric point. -/
theorem connectedSpace_residueFiberOver_of_geometricFiber
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ybar : GeometricPoint Y)
    (h : ConnectedSpace (Points (fieldFiber f ybar.toFieldValuedPoint)))
    (U : smallEtaleSite Y) (vbar : GeometricPoint (ofOver U.left))
    (hv : vbar.map U.hom = ybar) :
    ConnectedSpace (Points (residueFiberOver f U.hom vbar.toScheme.image)) :=
  sorry

/-- If every residue-field fibre of an étale scheme neighbourhood of a geometric
point is connected, then the geometric fibre is connected. -/
theorem connectedSpace_geometricFiber_of_residueFiberOver
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ybar : GeometricPoint Y)
    (h : ∀ (U : smallEtaleSite Y) (vbar : GeometricPoint (ofOver U.left)),
      vbar.map U.hom = ybar →
        ConnectedSpace (Points (residueFiberOver f U.hom vbar.toScheme.image))) :
    ConnectedSpace (Points (fieldFiber f ybar.toFieldValuedPoint)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
