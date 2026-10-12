/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Graph.Codimension
public import ReasLib.AlgebraicGeometry.Correspondence.Graph

@[expose] public section

open CategoryTheory TopologicalSpace
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Example 45.3.2 (1): for a morphism `f : Y ⟶ X` of smooth projective schemes and a
clopen decomposition of `X` into equidimensional strata `Xd d` of dimension `d`, the part of
the graph over `Xd d` has pure codimension `d`. -/
@[stacks 0FG1] #check
  (AlgebraicGeometry.AlgebraicCycle.graph_hasPureCodimension :
    ∀ {k : Type u} [Field k]
      {X Y : AlgebraicGeometry.SchemeOverField k}
      [AlgebraicGeometry.Smooth X.hom] [AlgebraicGeometry.Projective X.hom]
      [AlgebraicGeometry.Smooth Y.hom] [AlgebraicGeometry.Projective Y.hom]
      (Xd : ℕ → X.left.Opens) (hcover : iSup Xd = ⊤)
      (hdisjoint : Pairwise
        (fun d e ↦ Disjoint (Xd d : Set X.left) (Xd e : Set X.left)))
      (hclopen : ∀ d, IsClopen (Xd d : Set X.left))
      (hequidimensional : ∀ d, EquidimensionalSpace (Xd d))
      (hdimension : ∀ d, (Xd d : Set X.left).Nonempty →
        topologicalKrullDim (Xd d) = (d : WithBot ℕ∞))
      (f : Y ⟶ X),
      ∀ d, HasPureCodimension
        (Set.range (AlgebraicGeometry.SchemeOverField.graph f).base ∩
          (pullback.fst X.hom Y.hom).base ⁻¹' (Xd d : Set X.left)) d)

/- Example 45.3.2 (2): the graph cycle has degree-zero support. -/
@[stacks 0FG1] #check
  (AlgebraicGeometry.AlgebraicCycle.graph_isDegreeZeroCorrespondence :
    ∀ {k : Type u} [Field k]
      {X Y : AlgebraicGeometry.SchemeOverField k}
      [AlgebraicGeometry.Smooth X.hom] [AlgebraicGeometry.Projective X.hom]
      [AlgebraicGeometry.Smooth Y.hom] [AlgebraicGeometry.Projective Y.hom]
      (Xd : ℕ → X.left.Opens) (hcover : iSup Xd = ⊤)
      (hdisjoint : Pairwise
        (fun d e ↦ Disjoint (Xd d : Set X.left) (Xd e : Set X.left)))
      (hclopen : ∀ d, IsClopen (Xd d : Set X.left))
      (hequidimensional : ∀ d, EquidimensionalSpace (Xd d))
      (hdimension : ∀ d, (Xd d : Set X.left).Nonempty →
        topologicalKrullDim (Xd d) = (d : WithBot ℕ∞))
      (f : Y ⟶ X),
      AlgebraicGeometry.AlgebraicCycle.IsDegreeZeroCorrespondence Xd
        (AlgebraicGeometry.AlgebraicCycle.graph f))

/- Example 45.3.2 (3): the rational graph construction gives a concrete degree-zero bivariant
correspondence from `X` to `Y`. -/
@[stacks 0FG1] #check
  (AlgebraicGeometry.Correspondence.rationalGraph :
    ∀ {k : Type u} [Field k]
      {X Y : AlgebraicGeometry.SchemeOverField k}
      [AlgebraicGeometry.Smooth X.hom] [AlgebraicGeometry.Projective X.hom]
      [AlgebraicGeometry.Smooth Y.hom] [AlgebraicGeometry.Projective Y.hom]
      (f : Y ⟶ X),
      AlgebraicGeometry.BivariantClass.RationalBivariantClass (fun _ ↦ 0)
        (Limits.prod.snd : X ⨯ Y ⟶ Y) 0)
