module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap90.Example_90_15_3_Quotient
public import stacks_project.Chap90.Lemma_90_3_4_Length
public import stacks_project.Chap90.Remark_90_15_6_Hull
public import stacks_project.Chap90.Remark_90_15_7_IsoClass

/-!
# Versal images and hulls in fibrewise isomorphism classes

The canonical morphism from a predeformation category to its category of fibrewise
isomorphism classes is smooth, so it carries versal formal objects to versal formal
objects. If the differential is bijective, the image is a hull. In the separable
finite-tangent case such a hull exists.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace FormalObject

/-- If a formal object satisfies `BijectiveDifferential`, then so does its image in
the category of fibrewise isomorphism classes. -/
theorem bijectiveDifferential_isoClass [Functor.IsPredeformationCategory p]
    (ξ : FormalObject p) (h : BijectiveDifferential ξ) :
    BijectiveDifferential (isoClass ξ) :=
  sorry

/-- Remark 90.15.7 (1): if `ξ` is a versal formal object of a predeformation category
`p`, then its image `isoClass ξ` in `isoClassProjection p` is versal. -/
@[stacks 06IZ]
instance instIsVersal_isoClass [Functor.IsPredeformationCategory p]
    (ξ : FormalObject p) [IsVersal ξ] : IsVersal (isoClass ξ) :=
  sorry

/-- If `ξ` is a hull, then so is its image in the category of fibrewise isomorphism
classes. -/
instance instIsHull_isoClass [Functor.IsPredeformationCategory p]
    (ξ : FormalObject p) [IsHull ξ] : IsHull (isoClass ξ) :=
  sorry

/-- Remark 90.15.7 (2): if `ξ` is versal and `BijectiveDifferential ξ` holds, then
`isoClass ξ` is a hull of `isoClassProjection p`. -/
@[stacks 06IZ]
theorem isHull_isoClass [Functor.IsPredeformationCategory p]
    (ξ : FormalObject p) [IsVersal ξ] (h : BijectiveDifferential ξ) :
    IsHull (isoClass ξ) :=
  sorry

/-- Remark 90.15.7 (3): if `Algebra.residueImage Λ k ⊂ k` is separable and `p` is a
predeformation category satisfying (S1), (S2) and `FiniteDimensional k (tangentSpace p)`,
then `isoClassProjection p` admits a hull. -/
@[stacks 06IZ]
theorem exists_isHull_isoClass [Functor.IsPredeformationCategory p]
    [Functor.HasSchlessingerS2 p]
    (h_s1 : ∀ {x x1 x2 : F} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x),
      Function.Surjective (p.map f2).hom →
        ∃ (y : F) (π1 : y ⟶ x1) (π2 : y ⟶ x2),
          CommSq π1 π2 f1 f2 ∧
            IsPullback (p.map π1) (p.map π2) (p.map f1) (p.map f2))
    [AddCommGroup (Functor.tangentSpace p)]
    [Module k (Functor.tangentSpace p)]
    [FiniteDimensional k (Functor.tangentSpace p)]
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k] :
    ∃ ξ : FormalObject (Functor.isoClassProjection p), IsHull ξ :=
  sorry

end FormalObject
