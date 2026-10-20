/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Representable.Lifted
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Composition
public import ReasLib.CategoryTheory.Functor.OverIso

/-!
# Transport of representable categories fibred in groupoids

Representability under change of base and equivalence of total categories.
-/

@[expose] public section

universe u v wZ vZ wP vP wQ vQ

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids

/-- View a category fibred in groupoids over `Over U` as one over `C`. This is the slice-forget
specialization of the generic bundled composition `FiberedCategoryOver.Groupoids.comp`. -/
def absolutize {U : C}
    (Z : FiberedCategoryOver.Groupoids.{max u v, v, wZ, vZ} (Over U)) :
    FiberedCategoryOver.Groupoids.{u, v, wZ, vZ} C :=
  comp Z (Over.forget U)

/-- Absolutization retains the total category of the relative fibred category. -/
@[simp]
theorem absolutize.total {U : C}
    (Z : FiberedCategoryOver.Groupoids.{max u v, v, wZ, vZ} (Over U)) :
    (absolutize Z).total = Z.total := sorry

/-- The projection of an absolutized fibred category is the relative projection followed by the
slice-forget functor. -/
@[simp]
theorem absolutize.p {U : C}
    (Z : FiberedCategoryOver.Groupoids.{max u v, v, wZ, vZ} (Over U)) :
    (absolutize Z).p = Z.p ⋙ Over.forget U := sorry

/-- Representability in the ordinary fixed owner transports contravariantly along an equivalence
of total categories whose projection to the common base commutes up to natural isomorphism.

This is the convenient downstream form; it produces the standard bicategorical
`IsRepresentable` property without exposing universe lifts. -/
theorem IsRepresentable.ofTotalEquivalence
    {P Q : FiberedCategoryOver.Groupoids C}
    (hQ : Q.IsRepresentable)
    (e : P.total ⥤ Q.total) [e.IsEquivalence]
    (comm : e ⋙ Q.p ≅ P.p) :
    P.IsRepresentable := sorry
/- Proof strategy: choose a canonical slice presentation of `Q`, compose it with `e`, and
strictify the comparison over `C`; groupoid fibredness upgrades the total equivalence to a
bicategorical equivalence over the base. -/

/-- Ordinary representability is invariant under an equivalence of total categories equipped with
an isomorphism over the common base.

This symmetric form is for callers that retain an unbundled total functor and its projection
comparison.  Callers that already have a `Functor.OverIso` should use
`IsRepresentable.iff_ofOverIso`. -/
theorem IsRepresentable.iff_ofTotalEquivalence
    {P Q : FiberedCategoryOver.Groupoids C}
    (e : P.total ⥤ Q.total) [e.IsEquivalence]
    (comm : e ⋙ Q.p ≅ P.p) :
    P.IsRepresentable ↔ Q.IsRepresentable := sorry
/- Proof strategy: apply `IsRepresentable.ofTotalEquivalence` to `e` in one direction and to a
chosen quasi-inverse, equipped with the inverse projection comparison, in the other. -/

/-- Lifted representability transports along an equivalence of total categories even when the
source and target use different saturated owner universes. This is the universe-boundary
companion of `IsRepresentable.ofTotalEquivalence`. -/
theorem IsRepresentable.Lifted.ofTotalEquivalence
    {P : FiberedCategoryOver.Groupoids.{u, v,
      max wP (max u v), max vP v} C}
    {Q : FiberedCategoryOver.Groupoids.{u, v,
      max wQ (max u v), max vQ v} C}
    (hQ : IsRepresentable.Lifted Q)
    (e : P.total ⥤ Q.total) [e.IsEquivalence]
    (comm : e ⋙ Q.p ≅ P.p) :
    IsRepresentable.Lifted P := sorry
/- Proof strategy: choose a lifted slice presentation of `Q`, compose it with `e`, and strictify
the resulting comparison over `C`; groupoid fibredness upgrades it to an equivalence in the
source saturated owner. -/

/-- Lifted representability is invariant under an equivalence of total categories over the common
base, even when the two saturated owners have different total-category universes. -/
theorem IsRepresentable.Lifted.iff_ofTotalEquivalence
    {P : FiberedCategoryOver.Groupoids.{u, v,
      max wP (max u v), max vP v} C}
    {Q : FiberedCategoryOver.Groupoids.{u, v,
      max wQ (max u v), max vQ v} C}
    (e : P.total ⥤ Q.total) [e.IsEquivalence]
    (comm : e ⋙ Q.p ≅ P.p) :
    IsRepresentable.Lifted P ↔ IsRepresentable.Lifted Q := sorry
/- Proof strategy: apply `IsRepresentable.Lifted.ofTotalEquivalence` to `e` and to a chosen
quasi-inverse, using the inverse of the projection comparison for the reverse implication. -/

/-- Representability transports directly along an over-base functor whose underlying functor is
an equivalence. This is the bundled companion of `IsRepresentable.ofTotalEquivalence`; it keeps the
functor and its base comparison under one reusable owner. -/
theorem IsRepresentable.ofOverIso
    {P Q : FiberedCategoryOver.Groupoids C}
    (hQ : Q.IsRepresentable) (e : Functor.OverIso P.p Q.p)
    [e.functor.IsEquivalence] :
    P.IsRepresentable := sorry
/- Proof strategy: apply `IsRepresentable.ofTotalEquivalence hQ e.functor e.iso`. -/

/-- Representability is invariant under an over-base functor whose underlying functor is an
equivalence. -/
theorem IsRepresentable.iff_ofOverIso
    {P Q : FiberedCategoryOver.Groupoids C}
    (e : Functor.OverIso P.p Q.p) [e.functor.IsEquivalence] :
    P.IsRepresentable ↔ Q.IsRepresentable := sorry
/- Proof strategy: use `IsRepresentable.ofOverIso` for the forward implication and apply it to
`e.inverse` for the reverse implication. -/

/-- Lifted representability transports directly along an over-base functor whose underlying
functor is an equivalence, without forcing callers to unpack it into a total functor and a
separate base comparison. This is the universe-polymorphic companion of
`IsRepresentable.ofOverIso`. -/
theorem IsRepresentable.Lifted.ofOverIso
    {P : FiberedCategoryOver.Groupoids.{u, v,
      max wP (max u v), max vP v} C}
    {Q : FiberedCategoryOver.Groupoids.{u, v,
      max wQ (max u v), max vQ v} C}
    (hQ : IsRepresentable.Lifted Q) (e : Functor.OverIso P.p Q.p)
    [e.functor.IsEquivalence] :
    IsRepresentable.Lifted P := sorry
/- Proof strategy: apply `IsRepresentable.Lifted.ofTotalEquivalence hQ e.functor e.iso`. -/

/-- Lifted representability is invariant under an over-base functor whose underlying functor is
an equivalence. This is the bundled, cross-universe transport criterion for the lifted owner. -/
theorem IsRepresentable.Lifted.iff_ofOverIso
    {P : FiberedCategoryOver.Groupoids.{u, v,
      max wP (max u v), max vP v} C}
    {Q : FiberedCategoryOver.Groupoids.{u, v,
      max wQ (max u v), max vQ v} C}
    (e : Functor.OverIso P.p Q.p) [e.functor.IsEquivalence] :
    IsRepresentable.Lifted P ↔ IsRepresentable.Lifted Q := sorry
/- Proof strategy: apply `IsRepresentable.Lifted.ofOverIso` in both directions, using
`e.inverse` for the reverse direction. -/

end FiberedCategoryOver.Groupoids

end CategoryTheory
