module

public import stacks_project.Chap65.Lemma_65_16_3_Equivalence

/-!
# Lemma 65.16.3

Change of base scheme as an equivalence between algebraic spaces over `S` and
algebraic spaces over `S'` equipped with a morphism to `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 65.16.3: let `g : S ⟶ S'` be a morphism of the big fppf site. The assignment
sending an algebraic space `F` over `S` to the pair `(j_! F, j_! F ⟶ S)`, encoded as the
object `Over.mk (extendBaseHom g F)` of `Over (ofOver (Over.mk g))`, is an equivalence
between algebraic spaces over `S` and algebraic spaces `F'` over `S'` equipped with a
morphism `F' ⟶ S` of algebraic spaces over `S'`. -/
@[stacks 04SG]
def extendBaseEquivalence {S S' : Scheme.{u}} (g : S ⟶ S') :
    AlgebraicSpace S ≌ Over (ofOver (Over.mk g)) :=
  CategoryTheory.Equivalence.mk (extendBaseOver g) (restrictOverFunctor g)
    (extendBaseUnitIso g) (extendBaseCounitIso g)

/-- The forward functor of `extendBaseEquivalence g` is `extendBaseOver g`. -/
@[simp]
theorem extendBaseEquivalence_functor {S S' : Scheme.{u}} (g : S ⟶ S') :
    (extendBaseEquivalence g).functor = extendBaseOver g := sorry

/-- The inverse functor of `extendBaseEquivalence g` is `restrictOverFunctor g`. -/
@[simp]
theorem extendBaseEquivalence_inverse {S S' : Scheme.{u}} (g : S ⟶ S') :
    (extendBaseEquivalence g).inverse = restrictOverFunctor g := sorry

/-- On objects, the inverse of `extendBaseEquivalence g` is `restrictOver`. -/
@[simp]
theorem extendBaseEquivalence_inverse_obj {S S' : Scheme.{u}} (g : S ⟶ S')
    (X : Over (ofOver (Over.mk g))) :
    (extendBaseEquivalence g).inverse.obj X = restrictOver X := sorry

/-- `extendBaseOver g` is an equivalence of categories. -/
instance extendBaseOver_isEquivalence {S S' : Scheme.{u}} (g : S ⟶ S') :
    (extendBaseOver g).IsEquivalence :=
  (extendBaseEquivalence g).isEquivalence_functor

end AlgebraicGeometry.AlgebraicSpace
