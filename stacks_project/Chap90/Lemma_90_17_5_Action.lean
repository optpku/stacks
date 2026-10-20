module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Lifts.Torsor

open CategoryTheory
open Functor Fiber ArtinianLocalAlgCat IsLocalRing
open scoped TensorProduct

universe u v w

/- Compatibility view of the tangent tensor action on deformation lifts. -/
#check (CategoryTheory.Functor.liftsTensorVAdd :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type v} [Category.{w} F]
    {p : F ⥤ ArtinianLocalAlgCat Λ k} {A' A : ArtinianLocalAlgCat Λ k}
    [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ],
    tangentTensor f hI x0 → lifts p f x → lifts p f x)
