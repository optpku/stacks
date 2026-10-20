module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.EtaleFree
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

set_option maxHeartbeats 800000 in
/- Lemma 77.4.6: a finite-type morphism of algebraic spaces and a finite-type
quasi-coherent module, flat at every point of a fibre, admit an étale scheme
neighbourhood of the base point and an affine étale refinement of the stalk
pullback whose pulled-back module has free global sections and which covers
exactly the original fibre. -/
@[stacks 0CVW] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.existsEtaleCoverWithFreeSections_of_finiteType :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [FiniteType f]
      (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y)
      (h_flat : ∀ x : Points X, Points.map f x = y → flatOverAt F f x),
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
          let F' := (restrictToScheme V.left).obj ((Modules.pullback g).obj F)
          ∃ (_ : Set.range (Points.mapOfOver g ∘ p.fiberι x₀) = Points.map f ⁻¹' {y})
            (_ : IsAffine X'),
            Module.Free R (Scheme.Hom.globalSectionsMod p F' : ModuleCat R))
