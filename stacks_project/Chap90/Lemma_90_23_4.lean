module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap90.Definition_90_8_1_Smooth
public import stacks_project.Chap90.Definition_90_21_1_Groupoid
public import stacks_project.Chap90.Definition_90_23_1
public import stacks_project.Chap90.Definition_90_21_9_Quotient

/-!
# Smoothness of a groupoid in functors and of the quotient morphism

Lemma 90.23.4 records that smoothness of a groupoid in functors on
`ArtinianLocalAlgCat Λ k` is equivalent to smoothness of its source map, of
its target map, and of the quotient morphism `quotientMorphism G`.
-/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

/-- Lemma 90.23.4: for a groupoid in functors `(U, R, s, t, c)` on
`ArtinianLocalAlgCat Λ k`, the following are equivalent: the groupoid is
smooth; the source morphism `s : R ⟶ U` is smooth; the target morphism
`t : R ⟶ U` is smooth; and the quotient morphism `quotientMorphism G` is
smooth. -/
@[stacks 06KL]
theorem isSmooth_tfae (G : GroupoidInFunctors.{u + 1, u, v} (ArtinianLocalAlgCat Λ k)) :
    List.TFAE [IsSmooth G.s G.t, NatTrans.IsSmooth G.s, NatTrans.IsSmooth G.t,
      BasedFunctor.IsSmooth (quotientMorphism G)] :=
  sorry

/-- Smoothness of a groupoid in functors is equivalent to smoothness of the source
map. -/
theorem isSmooth_iff_source (G : GroupoidInFunctors.{u + 1, u, v} (ArtinianLocalAlgCat Λ k)) :
    IsSmooth G.s G.t ↔ NatTrans.IsSmooth G.s :=
  sorry

/-- Smoothness of a groupoid in functors is equivalent to smoothness of the target
map. -/
theorem isSmooth_iff_target (G : GroupoidInFunctors.{u + 1, u, v} (ArtinianLocalAlgCat Λ k)) :
    IsSmooth G.s G.t ↔ NatTrans.IsSmooth G.t :=
  sorry

/-- Smoothness of a groupoid in functors is equivalent to smoothness of the quotient
morphism `quotientMorphism G`. -/
theorem isSmooth_iff_quotientMorphism
    (G : GroupoidInFunctors.{u + 1, u, v} (ArtinianLocalAlgCat Λ k)) :
    IsSmooth G.s G.t ↔ BasedFunctor.IsSmooth (quotientMorphism G) :=
  sorry

end CategoryTheory.GroupoidInFunctors
