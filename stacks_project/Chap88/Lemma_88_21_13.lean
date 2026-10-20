module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.ClosedImmersion.RigSmoothRigSurjective
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Lemma 88.21.13: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
formal algebraic spaces. Assume that `X` and `Y` are locally Noetherian and
`f` is a closed immersion. The following are equivalent: `f` is rig-smooth
and rig-surjective; `f` is rig-étale and rig-surjective; for every affine
formal algebraic space `V` and every morphism `v : V ⟶ Y` which is
representable by algebraic spaces and étale, the morphism
`pullback.snd f v : X ×_Y V ⟶ V` corresponds to a surjective morphism of
adic Noetherian rings whose kernel `J` satisfies `I * J = ⊥` for some ideal
of definition `I`. -/
@[stacks 0GD6] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion.tfae_rigSmooth_rigSurjective :
    ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
      [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
      [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
      [ClosedImmersion f],
      List.TFAE
        [RigSmooth f ∧ RigSurjective f, RigEtale f ∧ RigSurjective f,
          ClosedImmersion.etaleAffine_kernelKilled f])
