module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SmallExtension
public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth
public import ReasLib.AlgebraicGeometry.FormalDeformation.Differential
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory
public import ReasLib.CategoryTheory.Fibered.Lifts

/-!
# Smoothness and the tangent differential

A morphism of deformation categories is smooth precisely when its tangent
differential is surjective and objects lift along small extensions whenever their
images lift.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat Functor
open ArtinianLocalAlgCat (IsSmallExtension)
open scoped Bicategory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F G : Type v} [Category.{w} F] [Category.{w} G]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}

namespace CategoryTheory.BasedFunctor

/-- Every fibre object lifts along a small extension whenever its image under the
based functor lifts along that extension. -/
def existsLiftOfImageLift (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) :
    Prop :=
  ∀ {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A) [IsSmallExtension f]
    (x : p.Fiber A),
      Nonempty (q.lifts f ((φ.fiberFunctor A).obj x)) → Nonempty (p.lifts f x)

/-- The image-lift condition is equivalent to the implication from existence of a
lift of the image to existence of a lift of each fibre object along every small extension. -/
theorem existsLiftOfImageLift_iff
    (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) :
    existsLiftOfImageLift φ ↔
      ∀ {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A) [IsSmallExtension f]
        (x : p.Fiber A),
          Nonempty (q.lifts f ((φ.fiberFunctor A).obj x)) →
            Nonempty (p.lifts f x) := Iff.rfl

/-- A morphism of deformation categories is smooth if and only if its tangent
differential is surjective and every fibre object lifts along a small extension
whenever its image lifts. -/
theorem isSmooth_iff_surjective_differential
    [Functor.IsDeformationCategory p] [Functor.IsDeformationCategory q]
    (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) :
    IsSmooth φ ↔
      Function.Surjective (differential φ) ∧
        existsLiftOfImageLift φ := sorry

/-- A morphism between deformation categories is smooth if its tangent differential
is surjective and its composite with a morphism to a category cofibered in groupoids
is smooth. -/
@[stacks 0E3R]
theorem isSmooth_of_comp_surjective_differential
    {H : Type v} [Category.{w} H] {r : H ⥤ ArtinianLocalAlgCat Λ k}
    [Functor.IsDeformationCategory p] [Functor.IsDeformationCategory q]
    [Functor.IsFibered.InGroupoids r.op]
    (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (ψ : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor r)
    (hsurj : Function.Surjective (differential φ))
    (hcomp : IsSmooth (φ ⋙ ψ)) : IsSmooth φ := sorry

end CategoryTheory.BasedFunctor
