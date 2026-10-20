module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase.MorphismProperty

/-!
# Lemma 65.16.5

Invariance of scheme-morphism properties of algebraic-space morphisms under the
change-of-base equivalence of Lemma 65.16.3.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 65.16.5: let `g : S ⟶ S'` be a morphism of the big fppf site, let `F` be an
algebraic space over `S`, let `T` be a scheme over `S`, and let `f : ofOver T ⟶ F` be a
morphism over `S`. Write `f' = extendBaseMap g f` for the morphism over `S'` obtained by
applying the equivalence of Lemma 65.16.3, so that the domain of `f'` is `T` viewed as a
scheme over `S'` via `Over.map g`. For any property `P` of morphisms of schemes as in
Definition 65.5.1, `(over P).presheaf f'` if and only if `(over P).presheaf f`. -/
@[stacks 03I6] #check (AlgebraicGeometry.AlgebraicSpace.extendBaseMap_over_presheaf_iff :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S')
    {F : AlgebraicSpace S} {T : Over S} (f : ofOver T ⟶ F)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget Scheme.fppfPrecoverage],
    (over P).presheaf (extendBaseMap g f) ↔ (over P).presheaf f)

/- Identifying the domain of `extendBaseMap g f` with `ofOver ((Over.map g).obj T)` via
`extendBasePresheafYonedaIso` does not change whether `f` has property `P`. -/
#check (AlgebraicGeometry.AlgebraicSpace.extendBaseMap_ofOver_over_presheaf_iff :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S')
    {F : AlgebraicSpace S} {T : Over S} (f : ofOver T ⟶ F)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget Scheme.fppfPrecoverage],
    (over P).presheaf ((extendBasePresheafYonedaIso g T).inv ≫ extendBaseMap g f) ↔
      (over P).presheaf f)

end AlgebraicGeometry.AlgebraicSpace
