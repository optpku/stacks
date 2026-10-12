/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.Zero
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w i

namespace CategoryTheory

/- Definition 59.13.1: the zeroth Čech cohomology object is the type of
families of sections agreeing on every pairwise pullback. -/
@[stacks 03NR] #check (CategoryTheory.cechH0 :
    ∀ {C : Type u} [Category.{v} C],
    (J : Coverage C) → (F : Cᵒᵖ ⥤ Type w) →
    ∀ {I : Type i} {X : I → C} {U : C},
    (π : ∀ i, X i ⟶ U) →
    (h𝒰 : Presieve.ofArrows X π ∈ J U) →
    [∀ i j, HasPullback (π i) (π j)] → Type (max i w))

#check (CategoryTheory.cechH0_compat :
    ∀ {C : Type u} [Category.{v} C],
    (J : Coverage C) → (F : Cᵒᵖ ⥤ Type w) →
    ∀ {I : Type i} {X : I → C} {U : C},
    (π : ∀ i, X i ⟶ U) →
    (h𝒰 : Presieve.ofArrows X π ∈ J U) →
    [∀ i j, HasPullback (π i) (π j)] →
    (s : CategoryTheory.cechH0 J F π h𝒰) → (i j : I) →
    F.map (pullback.fst (π i) (π j)).op (s.1 i) =
      F.map (pullback.snd (π i) (π j)).op (s.1 j))

end CategoryTheory
