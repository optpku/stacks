module

public import Mathlib.CategoryTheory.Category.Preorder
public import ReasLib.Algebra.Category.CommAlgCat.Over.FinitePresentation
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.Tactic.CrossRefAttribute

/-!
# Directed systems of finitely presented algebras

Every commutative algebra is a directed colimit of finitely presented algebras.  For a finite-type
target, the system may be chosen with surjective transition maps.  The index universe matches the
selected over-category, while the rings themselves need not live in the same universe.

@stack 00QN
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CommAlgCat.Over.FinitePresentation

/-- Lemma 10.127.2 (Tag 00QN) (1): every `R`-algebra is a directed colimit of finitely presented
`R`-algebras. -/
@[stacks 00QN "(1)"]
theorem exists_directedSystem (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A] :
    ∃ (I : Type (max u (v + 1))) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirectedOrder I)
      (F : I ⥤ category R A),
      Nonempty (IsColimit ((cocone R A).whisker F)) := sorry

/-- Lemma 10.127.2 (Tag 00QN) (2): if `A` is of finite type over `R`, its directed system of
finitely presented models can be chosen with surjective transition maps. -/
@[stacks 00QN "(2)"]
theorem exists_surjectiveSystem_of_finiteType (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A] [Algebra.FiniteType R A] :
    ∃ (I : Type (max u (v + 1))) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirectedOrder I)
      (F : I ⥤ category R A),
      (∀ ⦃i j : I⦄ (hij : i ≤ j),
        Function.Surjective ((F ⋙ diagram R A).map (homOfLE hij))) ∧
        Nonempty (IsColimit ((cocone R A).whisker F)) := sorry

end CommAlgCat.Over.FinitePresentation
