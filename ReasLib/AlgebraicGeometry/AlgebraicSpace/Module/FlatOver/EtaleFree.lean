/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.SpecStalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange

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
        let p := (Yoneda.fullyFaithful.preimage
          (V.hom ≫ Limits.pullback.snd f b :
            yoneda.obj V.left ⟶ yoneda.obj (specStalkOver N.toOver N.point))).left
        let x₀ := IsLocalRing.closedPoint R
        let F' := (restrictToScheme V.left).obj ((pullback g).obj F)
        ∃ (_ : Set.range (Points.mapOfOver g ∘ p.fiberι x₀) = Points.map f ⁻¹' {y})
          (_ : IsAffine X'),
          Module.Free R (Scheme.Hom.globalSectionsMod p F' : ModuleCat R) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
