/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap65.Lemma_65_16_3_Equivalence

/-!
# Lemma 65.16.5

Invariance of scheme-morphism properties of algebraic-space morphisms under the
change-of-base equivalence of Lemma 65.16.3.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 65.16.5: let `g : S ⟶ S'` be a morphism of the big fppf site, let `F` be an
algebraic space over `S`, let `T` be a scheme over `S`, and let `f : ofOver T ⟶ F` be a
morphism over `S`. Write `f' = extendBaseMap g f` for the morphism over `S'` obtained by
applying the equivalence of Lemma 65.16.3, so that the domain of `f'` is `T` viewed as a
scheme over `S'` via `Over.map g`. For any property `P` of morphisms of schemes as in
Definition 65.5.1, `(over P).presheaf f'` if and only if `(over P).presheaf f`. -/
@[stacks 03I6]
theorem extendBaseMap_over_presheaf_iff {S S' : Scheme.{u}} (g : S ⟶ S')
    {F : AlgebraicSpace S} {T : Over S} (f : ofOver T ⟶ F)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget Scheme.fppfPrecoverage] :
    (over P).presheaf (extendBaseMap g f) ↔ (over P).presheaf f :=
  sorry

/-- Identifying the domain of `extendBaseMap g f` with `ofOver ((Over.map g).obj T)` via
`extendBase_ofOver_functorOfPoints` does not change whether `f` has property `P`. -/
theorem extendBaseMap_ofOver_over_presheaf_iff {S S' : Scheme.{u}} (g : S ⟶ S')
    {F : AlgebraicSpace S} {T : Over S} (f : ofOver T ⟶ F)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget Scheme.fppfPrecoverage] :
    (over P).presheaf ((extendBase_ofOver_functorOfPoints g T).inv ≫ extendBaseMap g f) ↔
      (over P).presheaf f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
