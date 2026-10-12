/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber
public import ReasLib.CategoryTheory.Functor.IsomorphismClasses
public import stacks_project.Chap90.Definition_90_3_2_SmallExtension
public import stacks_project.Chap90.Definition_90_7_3
public import stacks_project.Chap90.Definition_90_10_1_Schlessinger
public import stacks_project.Chap90.Definition_90_16_8_Predeformation
public import stacks_project.Chap90.Definition_90_27_1_MinimalVersal

/-!
# Versal formal objects under Schlessinger's conditions

A formal object of a predeformation category satisfying (S1) and (S2) is versal
precisely when the induced map on dual-number fibre isomorphism classes is
surjective and every small-extension triangle in the completion admits a
ring-map fill-in on the complete local bases.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FormalObject

variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/-- Predeformation categories are cofibered in groupoids. -/
instance instIsFiberedInGroupoids_op [Functor.IsPredeformationCategory p] :
    Functor.IsFibered.InGroupoids p.op :=
  Functor.IsPredeformationCategory.isCofiberedInGroupoids

/-- A formal object `ξ` admits a base lift along small extensions if every
completion triangle over a small extension `B ⟶ A` of Artinian rings admits a
ring map `ξ.base ⟶ y.base` filling the base triangle. -/
def ExistsBaseLiftAlongSmallExtension [Functor.IsFibered.InGroupoids p.op]
    (ξ : FormalObject p) : Prop :=
  ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) [IsSmallExtension f]
    {y x : FormalObject p} (hxy : y ⟶ x),
      (Functor.completion p).IsHomLift (inclusion.map f) hxy →
        ∀ hξx : ξ ⟶ x, ∃ g : ξ.base ⟶ y.base, g ≫ hxy.base = hξx.base

/-- Unfolding of `ExistsBaseLiftAlongSmallExtension`. -/
theorem existsBaseLiftAlongSmallExtension_iff [Functor.IsFibered.InGroupoids p.op]
    (ξ : FormalObject p) :
    ExistsBaseLiftAlongSmallExtension ξ ↔
      ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) [IsSmallExtension f]
        {y x : FormalObject p} (hxy : y ⟶ x),
          (Functor.completion p).IsHomLift (inclusion.map f) hxy →
            ∀ hξx : ξ ⟶ x, ∃ g : ξ.base ⟶ y.base, g ≫ hxy.base = hξx.base :=
  sorry

/-- Lemma 90.13.2: let `p` be a predeformation category satisfying (S1) and (S2),
and let `ξ` be a formal object of `p` corresponding to a based functor
`φ : CompleteLocalAlgCat.identityProjection ξ.base ⥤ᵇ p`. Then `ξ` is versal if
and only if the induced map on dual-number fibre isomorphism classes is
surjective and `ξ` admits a ring-map fill-in along every small extension
triangle in the completion. -/
@[stacks 06IU]
theorem isVersal_iff [Functor.IsPredeformationCategory p]
    [Functor.HasSchlessingerS1 p] [Functor.HasSchlessingerS2 p] (ξ : FormalObject p)
    (φ : BasedCategory.ofFunctor (CompleteLocalAlgCat.identityProjection ξ.base) ⥤ᵇ
      BasedCategory.ofFunctor p)
    (hφ : Represents ξ φ) :
    IsVersal ξ ↔
      Function.Surjective (φ.fiberFunctor (dualNumber Λ k)).isoClassesMap ∧
        ExistsBaseLiftAlongSmallExtension ξ :=
  sorry

/-- A versal formal object induces a surjective map on dual-number fibre
isomorphism classes, for any representing based functor. -/
theorem IsVersal.surjective_differential {ξ : FormalObject p}
    [Functor.IsPredeformationCategory p] [IsVersal ξ]
    (φ : BasedCategory.ofFunctor (CompleteLocalAlgCat.identityProjection ξ.base) ⥤ᵇ
      BasedCategory.ofFunctor p)
    (hφ : Represents ξ φ) :
    Function.Surjective (φ.fiberFunctor (dualNumber Λ k)).isoClassesMap :=
  sorry

/-- A versal formal object admits a ring-map fill-in along every small extension
triangle in the completion. -/
theorem IsVersal.existsBaseLiftAlongSmallExtension
    [Functor.IsFibered.InGroupoids p.op] {ξ : FormalObject p} [IsVersal ξ] :
    ExistsBaseLiftAlongSmallExtension ξ :=
  sorry

end FormalObject
