/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import stacks_project.Chap95.Lemma_95_8_1

/-!
# Lemma 95.8.2

There exists a full subcategory `Spaces_ft,small ⊂ Spaces_ft` whose inclusion is fully
faithful and essentially surjective, and whose restricted projection is a stack over
`(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces

namespace FiniteType

/-- Lemma 95.8.2: there exists a subcategory `Spaces_ft,small ⊂ Spaces_ft` whose inclusion
functor `P.ι : Spaces_ft,small ⟶ Spaces_ft` is fully faithful (the canonical `Full`/`Faithful`
instances) and essentially surjective, and whose restricted projection
`p_ft,small = P.ι ⋙ (stack S).p` turns `Spaces_ft,small` into a stack over `(Sch/S)_fppf`.
Fiberwise `Small.{u}` is the big-site meaning of `ft,small`, since the ambient fibre is
only `EssentiallySmall.{u}`. -/
@[stacks 04UE]
theorem exists_smallSubcategory (S : Scheme.{u}) :
    ∃ P : ObjectProperty (stack S).total,
      P.ι.EssSurj ∧
        IsStack.OnSite (Scheme.fppfTopology.over S) (P.ι ⋙ (stack S).p) ∧
        ∀ U : Over S, Small.{u} ((P.ι ⋙ (stack S).p).Fiber U) := sorry

/-- Remark 8.4.9 condition (4): the fibre of `p_ft` over `U` is essentially small. -/
theorem fibers_essentiallySmall (S : Scheme.{u}) (U : Over S) :
    ObjectProperty.EssentiallySmall.{u} (⊤ : ObjectProperty ((p S).Fiber U)) := sorry

end FiniteType

end AlgebraicGeometry.AlgebraicSpace.Spaces
