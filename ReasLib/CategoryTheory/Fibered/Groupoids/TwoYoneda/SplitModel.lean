/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.TwoYoneda.Presheaf

/-!
# The split co-Grothendieck model of the two-Yoneda presheaf

This file owns the reducible co-Grothendieck model and the canonical split fibred-in-groupoids
instances. Evaluation back into the original category is defined in
`TwoYoneda.Comparison.Construction`.
-/

@[expose] public section

universe v u vS uS

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {S : Type uS} [Category.{vS} S]

namespace TwoYoneda

/-- The 2-Yoneda co-Grothendieck model as a based category over `C`. This reducible view keeps
the canonical `CoGrothendieck.forget` projection visible to downstream constructions. -/
abbrev splitModel (p : S ⥤ C) :=
  BasedCategory.ofFunctor
    (Pseudofunctor.CoGrothendieck.forget (presheaf p).toPseudofunctor')

/-- The total category of the 2-Yoneda co-Grothendieck model. This is a reducible type view used
when accessing the canonical `(base, fiber)` representation. -/
abbrev splitCategory (p : S ⥤ C) := (splitModel p).obj

/-- The projection of the 2-Yoneda co-Grothendieck model is fibred in groupoids. This
source-facing bridge also prevents opacity of `presheaf` and `Functor.toPseudofunctor'` from
hiding the pointwise groupoid instances from typeclass search. -/
instance splitModel.inGroupoids
    (p : S ⥤ C) [Functor.IsFibered.InGroupoids p] :
    Functor.IsFibered.InGroupoids (splitModel p).p := sorry
/- Proof strategy: unfold `splitModel`; apply
`Pseudofunctor.CoGrothendieck.forgetInGroupoids`. At a locally discrete object, reduce
`Functor.toPseudofunctor'_obj` and discharge the pointwise goal with
`presheaf.isGroupoid p`. Do not use bare `inferInstance` here, which would recurse. -/

/-- The canonical 2-Yoneda co-Grothendieck model is a split category fibred in groupoids. -/
instance splitModel.splitInGroupoids
    (p : S ⥤ C) [Functor.IsFibered.InGroupoids p] :
    Functor.IsFibered.Split.InGroupoids (splitModel p).p := sorry
/- Proof strategy: for splitness, use `presheaf p` itself when its universes align; otherwise
lift its value categories and use the canonical strict based-category isomorphism induced by the
lift equivalences. For groupoidality, use the preceding canonical
`splitModel.inGroupoids` instance. -/

end TwoYoneda

end CategoryTheory
