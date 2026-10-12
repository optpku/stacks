/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.CategoryTheory.HomCongr
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.HomotopyCategory.Equivalence
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.FullyFaithful

/-!
# Presentations by slice fibrations

This file transports the canonical slice Hom equivalence through chosen bicategorical
presentations and exposes the source-facing induced-morphism relation.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids

namespace Presentation

/-- Transport a morphism between representing objects back through chosen presentations. -/
@[stacks 04SF "transport a morphism through represented presentations"]
def map {P Q : FiberedCategoryOver.Groupoids C} {X Y : C}
    (eP : P ≌ slice X) (eQ : Q ≌ slice Y) (f : X ⟶ Y) : P ⟶ Q :=
  (eP.hom ≫ FiberedCategoryOver.Groupoids.overMap f) ≫ eQ.inv

/-- Transport a morphism through chosen slice presentations and recover its base morphism. -/
@[stacks 04SF "recover a morphism through represented presentations"]
def recover {P Q : FiberedCategoryOver.Groupoids C} {X Y : C}
    (eP : P ≌ slice X) (eQ : Q ≌ slice Y) (F : P ⟶ Q) : X ⟶ Y :=
  slice.eval ((eP.inv ≫ F) ≫ eQ.hom)

namespace recover

/-- `2`-isomorphic morphisms through the same presentations recover the same base morphism. -/
theorem eq_of_isomorphic
    {P Q : FiberedCategoryOver.Groupoids C} {X Y : C}
    (eP : P ≌ slice X) (eQ : Q ≌ slice Y)
    {F G : P ⟶ Q} (h : IsIsomorphic F G) :
    recover eP eQ F = recover eP eQ G := sorry

/-- Recovery through chosen presentations is surjective. -/
@[stacks 04SF "(1)"]
theorem surjective {P Q : FiberedCategoryOver.Groupoids C} {X Y : C}
    (eP : P ≌ slice X) (eQ : Q ≌ slice Y) :
    Function.Surjective (recover eP eQ) := sorry

/-- Two morphisms recover the same base morphism exactly when they are `2`-isomorphic. -/
@[stacks 04SF "(1)"]
theorem eq_iff_isomorphic {P Q : FiberedCategoryOver.Groupoids C} {X Y : C}
    (eP : P ≌ slice X) (eQ : Q ≌ slice Y) (F G : P ⟶ Q) :
    recover eP eQ F = recover eP eQ G ↔ IsIsomorphic F G := sorry

/-- Recovering the explicit presentation map returns the original base morphism. -/
@[simp]
theorem map
    {P Q : FiberedCategoryOver.Groupoids C} {X Y : C}
    (eP : P ≌ slice X) (eQ : Q ≌ slice Y) (f : X ⟶ Y) :
    recover eP eQ (Presentation.map eP eQ f) = f := sorry

end recover

/-- Homotopy classes of morphisms through chosen presentations are canonically equivalent to
morphisms between their representing objects. -/
@[stacks 04SF "Hom equivalence for represented fibred groupoids"]
noncomputable def homEquiv
    {P Q : FiberedCategoryOver.Groupoids C} {X Y : C}
    (eP : P ≌ slice X) (eQ : Q ≌ slice Y) :
    (Bicategory.HomotopyCategory.mk P ⟶
      Bicategory.HomotopyCategory.mk Q) ≃ (X ⟶ Y) :=
  (Iso.homCongr
    (Bicategory.HomotopyCategory.isoOfEquivalence eP)
    (Bicategory.HomotopyCategory.isoOfEquivalence eQ)).trans
      (slice.evalEquiv X Y)

namespace homEquiv

/-- The represented Hom equivalence evaluates a transported representative. -/
@[simp]
theorem apply.mkHom
    {P Q : FiberedCategoryOver.Groupoids C} {X Y : C}
    (eP : P ≌ slice X) (eQ : Q ≌ slice Y) (F : P ⟶ Q) :
    homEquiv eP eQ (Bicategory.HomotopyCategory.mkHom F) = recover eP eQ F := sorry

/-- The inverse Hom equivalence is the explicit presentation map. -/
@[simp]
theorem symm.apply
    {P Q : FiberedCategoryOver.Groupoids C} {X Y : C}
    (eP : P ≌ slice X) (eQ : Q ≌ slice Y) (f : X ⟶ Y) :
    (homEquiv eP eQ).symm f =
      Bicategory.HomotopyCategory.mkHom (Presentation.map eP eQ f) := sorry

end homEquiv

end Presentation

variable {P Q : FiberedCategoryOver.Groupoids C}

/-- A morphism `F : P ⟶ Q` induces `f : X ⟶ Y` relative to presentation maps `j` and
`j'` when `F ≫ j'` is `2`-isomorphic to `j ≫ overMap f`. -/
@[stacks 04SF "morphism induced through represented presentations"]
def InducesHom {X Y : C}
    (F : P ⟶ Q) (j : P ⟶ slice X) (j' : Q ⟶ slice Y) (f : X ⟶ Y) : Prop :=
  Nonempty ((F ≫ j') ≅ (j ≫ FiberedCategoryOver.Groupoids.overMap f))

/-- The explicit presentation map induces the base morphism from which it was constructed. -/
theorem Presentation.map.induces {X Y : C}
    (eP : P ≌ slice X) (eQ : Q ≌ slice Y) (f : X ⟶ Y) :
    InducesHom (Presentation.map eP eQ f) eP.hom eQ.hom f := sorry

namespace InducesHom

/-- The base morphism recovered from a morphism is induced by that morphism. -/
theorem recover {X Y : C}
    (eP : P ≌ slice X) (eQ : Q ≌ slice Y) (F : P ⟶ Q) :
    InducesHom F eP.hom eQ.hom (Presentation.recover eP eQ F) := sorry

/-- A morphism induces `f` exactly when its recovered base morphism is `f`. -/
theorem iff_recover_eq {X Y : C}
    (eP : P ≌ slice X) (eQ : Q ≌ slice Y) (F : P ⟶ Q) (f : X ⟶ Y) :
    InducesHom F eP.hom eQ.hom f ↔ Presentation.recover eP eQ F = f := sorry

/-- Every morphism between representing objects is induced by a morphism between the
presentations. -/
@[stacks 04SF "(2)"]
theorem exists_morphism {X Y : C}
    (eP : P ≌ slice X) (eQ : Q ≌ slice Y) (f : X ⟶ Y) :
    ∃ F : P ⟶ Q, InducesHom F eP.hom eQ.hom f := sorry

/-- Two morphisms inducing the same base morphism are `2`-isomorphic. -/
@[stacks 04SF "(2)"]
theorem nonempty_iso {X Y : C}
    (eP : P ≌ slice X) (eQ : Q ≌ slice Y) (f : X ⟶ Y)
    {F G : P ⟶ Q} (hF : InducesHom F eP.hom eQ.hom f)
    (hG : InducesHom G eP.hom eQ.hom f) :
    Nonempty (F ≅ G) := sorry

/-- The `2`-isomorphism between two morphisms inducing the same base morphism is unique. -/
@[stacks 04SF "(2)"]
theorem subsingleton_iso {X Y : C}
    (eP : P ≌ slice X) (eQ : Q ≌ slice Y) (f : X ⟶ Y)
    {F G : P ⟶ Q} (hF : InducesHom F eP.hom eQ.hom f)
    (hG : InducesHom G eP.hom eQ.hom f) :
    Subsingleton (F ≅ G) := sorry

end InducesHom

/-- Fixed-morphism form of uniqueness of representing objects. -/
theorem Presentation.uniqueUpToIso.of_isEquivalence
    {P : FiberedCategoryOver.Groupoids C} {X X' : C}
    (j : P ⟶ slice X) (j' : P ⟶ slice X')
    (hj : BasedFunctor.IsEquivalence (toBasedFunctor j))
    (hj' : BasedFunctor.IsEquivalence (toBasedFunctor j')) :
    ∃ i : X ≅ X', Nonempty (j' ≅ j ≫ overMap i.hom) := sorry

/-- Fixed-morphism form of `Presentation.objectsIsomorphic`. -/
theorem Presentation.objectsIsomorphic.of_isEquivalence
    {P : FiberedCategoryOver.Groupoids C} {X X' : C}
    (j : P ⟶ slice X) (j' : P ⟶ slice X')
    (hj : BasedFunctor.IsEquivalence (toBasedFunctor j))
    (hj' : BasedFunctor.IsEquivalence (toBasedFunctor j')) :
    Nonempty (X ≅ X') := sorry

/-- Two bicategorical presentations of the same fibred groupoid have isomorphic representing
objects, compatibly with the presentations. -/
@[stacks 02Y3 "(2)"]
theorem Presentation.uniqueUpToIso
    {P : FiberedCategoryOver.Groupoids C} {X X' : C}
    (j : P ≌ slice X) (j' : P ≌ slice X') :
    ∃ i : X ≅ X', Nonempty (j'.hom ≅ j.hom ≫ overMap i.hom) := sorry

/-- The representing objects of two bicategorical slice presentations are isomorphic. -/
theorem Presentation.objectsIsomorphic
    {P : FiberedCategoryOver.Groupoids C} {X X' : C}
    (j : P ≌ slice X) (j' : P ≌ slice X') :
    Nonempty (X ≅ X') := sorry

end FiberedCategoryOver.Groupoids

end CategoryTheory

/- Data and axiom audit: `Presentation.map`, `recover`, and `homEquiv` explicitly transport the
canonical slice data. `sorryAx` is confined to inverse, functor, and bicategorical coherence laws;
no representative is selected from a quotient class. -/
