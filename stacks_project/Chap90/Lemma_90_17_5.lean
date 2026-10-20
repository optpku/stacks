module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Lifts.Torsor
import StacksCheckRecall

open CategoryTheory
open Functor Fiber ArtinianLocalAlgCat IsLocalRing
open scoped TensorProduct

universe u v w

/- Lemma 90.17.5
For a deformation category, a surjection with maximal-ideal-annihilated kernel
gives every nonempty lift set a torsor under the tangent space tensored with
that kernel, using a chosen residue pushforward.
-/
@[stacks 06JI] #check (CategoryTheory.Functor.liftsAddTorsor :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type v} [Category.{w} F]
    {p : F ⥤ ArtinianLocalAlgCat Λ k} {A' A : ArtinianLocalAlgCat Λ k}
    [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ] [Nonempty (lifts p f x)],
    AddTorsor (tangentTensor f hI x0) (lifts p f x))
