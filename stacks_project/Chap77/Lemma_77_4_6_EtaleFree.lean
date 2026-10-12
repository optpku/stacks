/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver
public import stacks_project.Chap68.Definition_68_11_5_Neighborhood
public import stacks_project.Chap68.Lemma_68_22_3_SpecStalk

/-!
# Free global sections after an étale refinement of algebraic spaces

A finite-type quasi-coherent module on an algebraic space, flat along a fibre of a
finite-type morphism, becomes free on global sections after an étale scheme
neighbourhood of the base point and an affine étale refinement of the stalk pullback.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- A finite-type quasi-coherent module that is flat over the base along a fibre of a
finite-type morphism of algebraic spaces admits, after an étale scheme neighbourhood of
the base point, an affine étale refinement of the stalk pullback covering that fibre
and having free global sections. -/
@[stacks 0CVW]
theorem existsEtaleCoverWithFreeSections_of_finiteType {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [FiniteType f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y)
    (h_flat : ∀ x : Points X, Points.map f x = y → flatOverAt F f x) :
    ∃ N : EtaleNeighborhood Y y,
      let R := N.scheme.presheaf.stalk N.point
      let b := fromSpecStalk N.hom N.point
      let P := Limits.pullback f b
      ∃ V : smallEtaleSite P,
        let X' := V.left.left
        let g := V.hom ≫ Limits.pullback.fst f b
        let p := (toOverHom (V.hom ≫ Limits.pullback.snd f b)).left
        let x₀ := IsLocalRing.closedPoint R
        let F' := (restrictToScheme V).obj ((pullback (Limits.pullback.fst f b)).obj F)
        ∃ (_ : Set.range (Points.mapOfOver g ∘ p.fiberι x₀) = Points.map f ⁻¹' {y})
          (_ : IsAffine X'),
          Module.Free R (Scheme.Hom.globalSectionsMod p F' : ModuleCat R) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
