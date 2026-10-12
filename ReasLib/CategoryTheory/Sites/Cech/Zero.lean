/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Coverage

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w i

namespace CategoryTheory

/-- The zeroth Čech cohomology object for a chosen covering family is the subtype
of families of sections whose restrictions agree on every pairwise pullback. -/
def cechH0
    {C : Type u} [Category.{v} C]
    (J : Coverage C) (F : Cᵒᵖ ⥤ Type w)
    {I : Type i} {X : I → C} {U : C}
    (π : ∀ i, X i ⟶ U)
    (h𝒰 : Presieve.ofArrows X π ∈ J U)
    [∀ i j, HasPullback (π i) (π j)] :
    Type (max i w) :=
  {s : ∀ i, F.obj (op (X i)) //
    ∀ i j,
      F.map (pullback.fst (π i) (π j)).op (s i) =
        F.map (pullback.snd (π i) (π j)).op (s j)}

/-- A family in the zeroth Čech cohomology object satisfies the pairwise
compatibility equation on every pullback in the covering family. -/
theorem cechH0_compat
    {C : Type u} [Category.{v} C]
    (J : Coverage C) (F : Cᵒᵖ ⥤ Type w)
    {I : Type i} {X : I → C} {U : C}
    (π : ∀ i, X i ⟶ U)
    (h𝒰 : Presieve.ofArrows X π ∈ J U)
    [∀ i j, HasPullback (π i) (π j)]
    (s : cechH0 J F π h𝒰) (i j : I) :
    F.map (pullback.fst (π i) (π j)).op (s.1 i) =
      F.map (pullback.snd (π i) (π j)).op (s.1 j) := sorry

end CategoryTheory
