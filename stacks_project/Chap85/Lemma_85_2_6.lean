module

public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import stacks_project.Chap85.Lemma_85_2_5

/-!
# Lemma 85.2.6

Restriction of injective abelian sheaves from `X_Zar` to a degree-`n`
component `X_n`.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

noncomputable section

universe u

namespace CategoryTheory.SimplicialObject

/-- Lemma 85.2.6: if `I` is an injective abelian sheaf on `X_Zar`, then its
restriction `I_n` is an injective abelian sheaf on `X_n`. -/
@[stacks 09W1, instance]
instance sheafComponent_preservesInjectiveObjects
    (X : SimplicialObject TopCat.{u}) (n : ℕ) :
    (sheafComponent X n AddCommGrpCat.{u}).PreservesInjectiveObjects :=
  sorry

/-- Restriction of an injective abelian sheaf on `X_Zar` along the degree-`n`
component inclusion is injective on `X_n`. -/
theorem injective_sheafComponent
    (X : SimplicialObject TopCat.{u}) (n : ℕ)
    (I : Sheaf (zariskiTopology X) AddCommGrpCat.{u})
    [Injective I] :
    Injective ((sheafComponent X n AddCommGrpCat.{u}).obj I) :=
  sorry

end CategoryTheory.SimplicialObject

