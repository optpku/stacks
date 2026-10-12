/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_3_2_SmallExtension
public import stacks_project.Chap90.Definition_90_7_3
public import stacks_project.Chap90.Definition_90_27_1_MinimalVersal

/-!
# Versality via infinitesimal fill-in in the completion

Versality of a formal object is the infinitesimal fill-in property in the
completion along Artinian surjections, equivalently along small extensions, and
is independent of a choice of representing based functor.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FormalObject

variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k} [Functor.IsFibered.InGroupoids p.op]

/-- Remark 90.8.10 (1): versality of a formal object `ξ` of a category cofibered in
groupoids over `ArtinianLocalAlgCat Λ k` is equivalent to the following fill-in
property in the completion: if `hxy : y ⟶ x` lies over a surjection `f : B ⟶ A`
of Artinian local algebras and `hξx : ξ ⟶ x`, then there exists `hξy : ξ ⟶ y`
with `hξy ≫ hxy = hξx`. -/
@[stacks 06HS]
theorem isVersal_iff_exists_lift (ξ : FormalObject p) :
    IsVersal ξ ↔
      ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A), Function.Surjective f.hom →
        ∀ {y x : FormalObject p} (hxy : y ⟶ x),
          (Functor.completion p).IsHomLift (inclusion.map f) hxy →
            ∀ (hξx : ξ ⟶ x), ∃ hξy : ξ ⟶ y, hξy ≫ hxy = hξx :=
  sorry

/-- Versality of a formal object is equivalent to the same fill-in property in the
completion restricted to small extensions. -/
theorem isVersal_iff_exists_lift_isSmallExtension (ξ : FormalObject p) :
    IsVersal ξ ↔
      ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) [IsSmallExtension f]
        {y x : FormalObject p} (hxy : y ⟶ x),
          (Functor.completion p).IsHomLift (inclusion.map f) hxy →
            ∀ (hξx : ξ ⟶ x), ∃ hξy : ξ ⟶ y, hξy ≫ hxy = hξx :=
  sorry

/-- A versal formal object fills in every completion triangle whose vertical arrow
lies over a surjection of Artinian local algebras. -/
theorem IsVersal.exists_lift {ξ : FormalObject p} [IsVersal ξ]
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) (hf : Function.Surjective f.hom)
    {y x : FormalObject p} (hxy : y ⟶ x)
    (hover : (Functor.completion p).IsHomLift (inclusion.map f) hxy)
    (hξx : ξ ⟶ x) :
    ∃ hξy : ξ ⟶ y, hξy ≫ hxy = hξx :=
  sorry

/-- Remark 90.8.10 (2): versality of `ξ` is equivalent to smoothness of any based
functor `φ` representing `ξ`, and therefore does not depend on the choices of
pushforwards used to construct a representing morphism from the restricted
coyoneda of `ξ.base`. -/
@[stacks 06HS]
theorem isVersal_iff_isSmooth (ξ : FormalObject p)
    {φ : BasedCategory.ofFunctor (CompleteLocalAlgCat.identityProjection ξ.base) ⥤ᵇ
      BasedCategory.ofFunctor p}
    (hφ : Represents ξ φ) :
    IsVersal ξ ↔ BasedFunctor.IsSmooth φ :=
  sorry

end FormalObject
