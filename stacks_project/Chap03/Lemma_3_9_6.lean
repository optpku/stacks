module

public import stacks_project.Chap03.Lemma_3_9_4_Size
public import Mathlib.AlgebraicGeometry.Limits

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Cardinal AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Lemma 3.9.6. For morphisms of schemes `f : X ⟶ S` and `g : Y ⟶ S`, the size of the fibre
product `pullback f g` is at most `max X.size Y.size`. -/
@[stacks 04T6]
theorem size_pullback_le {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    (pullback f g).size ≤ max X.size Y.size := sorry

/-- The size of any scheme presenting a fibre product of `f : X ⟶ S` and `g : Y ⟶ S` is at most
`max X.size Y.size`. -/
theorem size_le_of_isPullback {X Y S P : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {fst : P ⟶ X} {snd : P ⟶ Y} (h : IsPullback fst snd f g) :
    P.size ≤ max X.size Y.size := sorry

end AlgebraicGeometry.Scheme
