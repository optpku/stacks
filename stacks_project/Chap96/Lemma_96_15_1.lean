module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import stacks_project.Chap96.Lemma_96_15_1_Abelian
public import stacks_project.Chap96.Lemma_96_15_1_Equivalence
public import stacks_project.Chap96.Lemma_96_15_1_Tensor
import StacksCheckRecall

/-!
# Lemma 96.15.1

Quasi-coherent modules on an algebraic stack are equivalent to equivariant
quasi-coherent modules on a presentation, form an abelian category with
colimits agreeing with `Mod(𝒪_𝒳)`, and are closed under tensor, internal Hom
from a finite locally free module, and extensions. The inclusion into
`Mod(𝒪_𝒳)` is right exact but not exact in general.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
  CategoryTheory.Functor CategoryTheory.Limits CategoryTheory.ObjectProperty
  FiberedCategoryOver.Groupoids AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

/- Lemma 96.15.1 (1): if `[U / R] ⟶ 𝒳` is a presentation of the algebraic stack
`𝒳` then there is a canonical equivalence `QCoh(𝒪_𝒳) ≌ QCoh(U, R, s, t, c)`. -/
@[stacks 06WV] #check presentationEquivalence

/- Lemma 96.15.1 (2): the category `QCoh(𝒪_𝒳)` is abelian. -/
@[stacks 06WV] #check abelian

/-- Lemma 96.15.1 (3): the inclusion functor `QCoh(𝒪_𝒳) ⟶ Mod(𝒪_𝒳)` is not exact
in general. -/
@[stacks 06WV]
theorem inclusion_not_exact :
    ¬ exactFunctor
        (QCoh (GroupoidsOver.slice (Over.mk (𝟙 (Spec (CommRingCat.of ℤ))))))
        (RingedSite.ModuleCat (fppfRingedSite _)) (inclusion _) :=
  sorry

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- Lemma 96.15.1 (3): the inclusion functor `QCoh(𝒪_𝒳) ⟶ Mod(𝒪_𝒳)` is right
exact. -/
@[stacks 06WV]
theorem inclusion_rightExact [AlgebraicStack X] :
    rightExactFunctor (QCoh X) (RingedSite.ModuleCat.{u} (fppfRingedSite X))
      (inclusion X) :=
  sorry

/-- Lemma 96.15.1 (4): the category `QCoh(𝒪_𝒳)` has colimits of every
universe-compatible shape. -/
@[stacks 06WV]
instance algebraicStack_hasColimitsOfShape [AlgebraicStack X]
    (J : Type u) [Category.{u} J] :
    HasColimitsOfShape J (QCoh X) :=
  sorry

/-- Lemma 96.15.1 (4): colimits in `QCoh(𝒪_𝒳)` agree with colimits in
`Mod(𝒪_𝒳)`. -/
@[stacks 06WV]
instance inclusion_preservesColimitsOfShape [AlgebraicStack X]
    (J : Type u) [Category.{u} J] :
    PreservesColimitsOfShape J (inclusion X) :=
  sorry

/- Lemma 96.15.1 (3): the inclusion `QCoh(𝒪_𝒳) ⟶ Mod(𝒪_𝒳)` preserves finite
colimits, hence is right exact. -/
@[stacks 06WV] #check inclusion_preservesFiniteColimits

/- Lemma 96.15.1 (4): colimits in `QCoh(𝒪_𝒳)` agree with colimits in
`Mod(𝒪_𝒳)` via the inclusion comparison. -/
@[stacks 06WV] #check inclusion_colimitIso

/- Lemma 96.15.1 (5): the tensor product of two quasi-coherent `𝒪_𝒳`-modules,
computed in `Mod(𝒪_𝒳)`, is an object of `QCoh(𝒪_𝒳)`. -/
@[stacks 06WV] #check tensor

/- Lemma 96.15.1 (5): the commutative fppf tensor comparison of that object is
an isomorphism. -/
@[stacks 06WV] #check tensorComparison_isIso

/- Lemma 96.15.1 (6): if `F` is finite locally free, internal Hom from `F` to
`G` in `Mod(𝒪_𝒳)` is an object of `QCoh(𝒪_𝒳)`. -/
@[stacks 06WV] #check internalHom

/- Lemma 96.15.1 (7): quasi-coherent modules on an algebraic stack are closed
under extensions in `Mod(𝒪_𝒳)`. -/
@[stacks 06WV] #check closedUnderExtensions

end AlgebraicGeometry.GroupoidsOver.QCoh
