module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Lifts.Functoriality
import StacksCheckRecall

noncomputable section

open CategoryTheory
open Functor Fiber ArtinianLocalAlgCat IsLocalRing BasedCategory
open scoped Bicategory TensorProduct

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F G : Type v} [Category.{w} F] [Category.{w} G]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}

/- Remark 90.17.6 The canonical action on lifts is functorial under morphisms of
deformation categories, with the induced differential acting on the tangent factor. -/
@[stacks 06JJ] #check (CategoryTheory.BasedFunctor.liftsTensorVAdd_map :
    ∀ [IsDeformationCategory p] [IsDeformationCategory q]
    {A' A : ArtinianLocalAlgCat Λ k}
    (Φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) (f : A' ⟶ A)
    (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ]
    (θ : tangentTensor f hI x0) (x' : lifts p f x),
    liftsMap Φ f x (liftsTensorVAdd f hf hI x ψ θ x') =
      BasedFunctor.liftsTensorVAdd_image Φ f hf hI x ψ (BasedFunctor.tangentTensorMap Φ f hI x0 θ)
        (liftsMap Φ f x x'))
