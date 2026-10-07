module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import stacks_project.Chap95.Lemma_95_5_1

/-!
# Lemma 95.5.3

There exists a full subcategory `QCoh_fg,small ⊂ QCoh_fg` whose inclusion is fully
faithful and essentially surjective, and whose restricted projection is a stack over
`(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.QCohStack.FG

/-- Lemma 95.5.3: there exists a subcategory `QCoh_fg,small ⊂ QCoh_fg` whose inclusion
functor `P.ι : QCoh_fg,small ⟶ QCoh_fg` is fully faithful (the canonical `Full`/`Faithful`
instances) and essentially surjective, and whose restricted projection
`p_fg,small = P.ι ⋙ (stack S).p` turns `QCoh_fg,small` into a stack over `(Sch/S)_fppf`.
Fiberwise `Small.{u}` is the big-site meaning of `fg,small`, since the ambient fibre is
only `EssentiallySmall.{u}`. -/
@[stacks 04U6]
theorem exists_smallSubcategory (S : Scheme.{u}) :
    ∃ P : ObjectProperty (stack S).total,
      P.ι.EssSurj ∧
        IsStack.OnSite (Scheme.fppfTopology.over S) (P.ι ⋙ (stack S).p) ∧
        ∀ U : Over S, Small.{u} ((P.ι ⋙ (stack S).p).Fiber U) := sorry

/-- Remark 8.4.9 condition (4): the fibre of `p_fg` over `U` is essentially small. -/
theorem fibers_essentiallySmall (S : Scheme.{u}) (U : Over S) :
    ObjectProperty.EssentiallySmall.{u} (⊤ : ObjectProperty ((p S).Fiber U)) := sorry

end AlgebraicGeometry.QCohStack.FG
