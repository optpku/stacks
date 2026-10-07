module

public import Mathlib.CategoryTheory.Category.ULift
public import stacks_project.Chap90.Definition_90_3_1_Classical
public import stacks_project.Chap90.Remark_90_15_6_Hull
public import stacks_project.Chap90.Remark_90_15_7_IsoClass
public import stacks_project.Chap93.Lemma_93_7_3

/-!
# Hulls of isomorphism classes of graded-algebra deformations

In the classical case, if `P` is a finitely generated graded `k`-algebra, the
set-valued functor of isomorphism classes of objects of `Def_P` admits a hull.
-/

@[expose] public section

open CategoryTheory Functor

noncomputable section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (Λ)

namespace FiniteProjectiveGradedAlgebraCat

/-- Hom-universe lift of the slice projection of `Def_P`, matching the object/hom
constraint of `FormalObject`. -/
abbrev deformationForgetULift (P : FiniteProjectiveGradedAlgebra k) :
    ULiftHom.{u + 1} (deformationCategory Λ k P) ⥤ ArtinianLocalAlgCat Λ k :=
  ULiftHom.down ⋙ deformationForget Λ P

/-- `deformationForgetULift` is `ULiftHom.down` followed by `deformationForget`. -/
theorem deformationForgetULift_eq (P : FiniteProjectiveGradedAlgebra k) :
    deformationForgetULift Λ P = ULiftHom.down ⋙ deformationForget Λ P := sorry

/-- Evaluating `deformationForgetULift` on a Hom-universe lift recovers
`deformationForget`. -/
theorem deformationForgetULift_obj (P : FiniteProjectiveGradedAlgebra k)
    (ξ : deformationCategory Λ k P) :
    (deformationForgetULift Λ P).obj (ULiftHom.objUp ξ) =
      (deformationForget Λ P).obj ξ := sorry

/-- The Hom-universe lift of the slice projection of `Def_P` is a predeformation
category. -/
instance instIsPredeformationCategory_deformationForgetULift
    (P : FiniteProjectiveGradedAlgebra k) :
    IsPredeformationCategory (deformationForgetULift Λ P) := sorry

/-- Predeformation categories are cofibered in groupoids. -/
instance instIsFiberedInGroupoids_deformationForgetULift_op
    (P : FiniteProjectiveGradedAlgebra k) :
    IsFibered.InGroupoids (deformationForgetULift Λ P).op :=
  IsPredeformationCategory.isCofiberedInGroupoids

/-- Lemma 93.7.4
In Example 93.7.1, if `P` is a finitely generated graded `k`-algebra and `Λ` is
complete local with residue field `k` (the classical case), then the functor
sending `A` to the isomorphism classes of objects of `(deformationForget Λ P).Fiber A`,
i.e. `Ob(Def_P(A))/≅`, has a hull. Equivalently, there exists a hull of the
associated cofibered set `isoClassProjection (deformationForgetULift Λ P)`. -/
@[stacks 0ET3]
theorem exists_isHull_isoClass (P : FiniteProjectiveGradedAlgebra k)
    [Algebra.FiniteType k P.carrier] [ArtinianLocalAlgCat.IsClassical Λ k] :
    ∃ ξ : FormalObject (isoClassProjection (deformationForgetULift Λ P)),
      FormalObject.IsHull ξ := sorry

end FiniteProjectiveGradedAlgebraCat
