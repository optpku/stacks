module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exactness of skyscraper sheaves at a point

This file records the additive exactness and the functorial splitting of the fiber--skyscraper
adjunction.  The statements live with the canonical site-point functors, independently of any
particular ringed site or textbook chapter.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u v w

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (p : Point.{w} J)

/-- The skyscraper-sheaf functor at a point preserves epimorphisms of abelian groups. -/
instance skyscraperSheafFunctor_preservesEpimorphisms :
    (p.skyscraperSheafFunctor :
      AddCommGrpCat.{w} ⥤ Sheaf J AddCommGrpCat.{w}).PreservesEpimorphisms := sorry

/-- Lemma 18.37.1 (05V7) (1): the skyscraper-sheaf functor
`p_* : AddCommGrpCat ⥤ Sheaf J AddCommGrpCat` is exact. -/
@[stacks 05V7 "(1)"]
theorem skyscraperSheafFunctor_exact :
    exactFunctor AddCommGrpCat.{w} (Sheaf J AddCommGrpCat.{w})
      p.skyscraperSheafFunctor := sorry

/-- Lemma 18.37.1 (05V7) (2): the counit of the fiber--skyscraper adjunction on abelian
sheaves is split epic as a natural transformation.  This is the categorical form of the
functorial decomposition `p⁻¹(p_* A) ≅ A ⊞ I(A)`. -/
@[stacks 05V7 "(2)"]
instance skyscraperSheafAdjunction_counit_isSplitEpi :
    IsSplitEpi
      (p.skyscraperSheafAdjunction.counit :
        p.skyscraperSheafFunctor ⋙ p.sheafFiber ⟶ 𝟭 AddCommGrpCat.{w}) := sorry

end CategoryTheory.GrothendieckTopology.Point
