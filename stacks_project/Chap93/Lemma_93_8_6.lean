/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap90.Definition_90_3_1_Classical
public import stacks_project.Chap90.Remark_90_15_6_Hull
public import stacks_project.Chap90.Remark_90_15_7_IsoClass
public import stacks_project.Chap93.Lemma_93_8_3_Deformation

/-!
# Hull of isomorphism classes of ring deformations

In Example 93.8.1, if `P` is a finite type `k`-algebra whose spectrum is smooth
over `k` except at finitely many points, and `Λ` is classical, then the functor
of isomorphism classes of objects of `Def_P` has a hull.
-/

@[expose] public section

open Algebra CategoryTheory Functor

noncomputable section

universe u

namespace FlatAlgebraCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- Hom-universe lift of the slice projection of `Def_P`, matching the object/hom
constraint of `FormalObject`. -/
abbrev deformationForgetULift (P : Type u) [CommRing P] [Algebra k P] :
    ULiftHom.{u + 1} (deformationCategory Λ k P) ⥤ ArtinianLocalAlgCat Λ k :=
  ULiftHom.down ⋙ deformationForget Λ k P

/-- `deformationForgetULift` is `ULiftHom.down` followed by `deformationForget`. -/
theorem deformationForgetULift_eq (P : Type u) [CommRing P] [Algebra k P] :
    deformationForgetULift Λ k P = ULiftHom.down ⋙ deformationForget Λ k P :=
  sorry

/-- Evaluating `deformationForgetULift` on a Hom-universe lift recovers
`deformationForget`. -/
theorem deformationForgetULift_obj (P : Type u) [CommRing P] [Algebra k P]
    (ξ : deformationCategory Λ k P) :
    (deformationForgetULift Λ k P).obj (ULiftHom.objUp ξ) =
      (deformationForget Λ k P).obj ξ :=
  sorry

/-- The Hom-universe lift of the slice projection of `Def_P` is a predeformation
category. -/
instance instIsPredeformationCategory_deformationForgetULift
    (P : Type u) [CommRing P] [Algebra k P] :
    IsPredeformationCategory (deformationForgetULift Λ k P) :=
  sorry

/-- Predeformation categories are cofibered in groupoids. -/
instance instIsFiberedInGroupoids_deformationForgetULift_op
    (P : Type u) [CommRing P] [Algebra k P] :
    IsFibered.InGroupoids (deformationForgetULift Λ k P).op :=
  IsPredeformationCategory.isCofiberedInGroupoids

/-- Lemma 93.8.6
In Example 93.8.1 assume `P` is a finite type `k`-algebra such that
`Spec(P) ⟶ Spec(k)` is smooth except at a finite number of points, recorded as
`(smoothLocus k P)ᶜ.Finite`. Assume `Λ` is a complete local ring with residue
field `k` (the classical case `ArtinianLocalAlgCat.IsClassical Λ k`). Then the
functor `F` sending `A` to the isomorphism classes of objects of `Def_P(A)`,
i.e. `(fiberIsoClassFunctor (deformationForget Λ k P)).obj A`, has a hull.
Equivalently, there exists a hull of the associated cofibered set
`isoClassProjection (deformationForgetULift Λ k P)`. -/
@[stacks 0ET4]
theorem exists_isHull_isoClass (P : Type u) [CommRing P] [Algebra k P]
    [Algebra.FiniteType k P] [ArtinianLocalAlgCat.IsClassical Λ k]
    (h_nonsmooth : (smoothLocus k P)ᶜ.Finite) :
    ∃ ξ : FormalObject (isoClassProjection (deformationForgetULift Λ k P)),
      FormalObject.IsHull ξ :=
  sorry

end FlatAlgebraCat
