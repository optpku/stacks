module

public import stacks_project.Chap90.Definition_90_3_2_SmallExtension
public import stacks_project.Chap90.Definition_90_8_1_Smooth
public import stacks_project.Chap90.Definition_90_12_3
public import stacks_project.Chap90.Definition_90_16_8_RimSchlessinger
public import stacks_project.Chap90.Definition_90_17_1_ObjectLift

/-!
# Smoothness of a map of deformation categories

A morphism of deformation categories is smooth if and only if its differential on
tangent spaces is surjective and lifts along small extensions exist whenever they
exist for the image object.
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
variable [IsPredeformationCategory p] [HasRimSchlessinger p]
variable [IsPredeformationCategory q] [HasRimSchlessinger q]
variable (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)

namespace CategoryTheory.BasedFunctor

/-- A predeformation category is cofibered in groupoids. -/
instance instIsFiberedInGroupoids_op {E : Type v} [Category.{w} E]
    {r : E ⥤ ArtinianLocalAlgCat Λ k} [IsPredeformationCategory r] :
    IsFibered.InGroupoids r.op :=
  IsPredeformationCategory.isCofiberedInGroupoids

/-- For every small extension `A' ⟶ A` and fibre object `x` over `A`, a lift of the
image of `x` along `f` implies a lift of `x` along `f`. -/
def existsLiftOfImageLift : Prop :=
  ∀ {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A) [IsSmallExtension f]
    (x : p.Fiber A),
      Nonempty (q.lifts f ((φ.fiberFunctor A).obj x)) → Nonempty (p.lifts f x)

/-- Unfolding of `existsLiftOfImageLift`. -/
theorem existsLiftOfImageLift_iff :
    existsLiftOfImageLift φ ↔
      ∀ {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A) [IsSmallExtension f]
        (x : p.Fiber A),
          Nonempty (q.lifts f ((φ.fiberFunctor A).obj x)) →
            Nonempty (p.lifts f x) := sorry

/-- Lemma 90.20.3: let `φ` be a morphism of deformation categories, and let `x0` be an
object of the residue fibre of the source with image `y0` in the residue fibre of the
target. Then `φ` is smooth if and only if the induced map `TF → TG` given by
`differential φ` is surjective and, for every small extension `A' ⟶ A` and every
fibre object `x` over `A`, a lift of the image of `x` to `A'` implies a lift of `x` to
`A'` (and vice versa). -/
@[stacks 0DYP]
theorem isSmooth_iff_surjective_differential :
    IsSmooth φ ↔
      Function.Surjective (differential φ) ∧
        existsLiftOfImageLift φ := sorry

/-- Surjectivity of the differential together with the small-extension image-lift
condition implies smoothness. -/
theorem isSmooth_of_surjective_differential
    (hsurj : Function.Surjective (differential φ))
    (hlift : existsLiftOfImageLift φ) : IsSmooth φ := sorry

/-- A smooth morphism of deformation categories has surjective differential. -/
theorem IsSmooth.surjective_differential [IsSmooth φ] :
    Function.Surjective (differential φ) := sorry

/-- A smooth morphism of deformation categories lifts an object along a small
extension whenever its image lifts. -/
theorem IsSmooth.existsLiftOfImageLift [IsSmooth φ] : existsLiftOfImageLift φ :=
  sorry

end CategoryTheory.BasedFunctor
