module

public import stacks_project.Chap90.Lemma_90_10_8_Pullback
public import stacks_project.Chap90.Lemma_90_10_8_Comparison
public import stacks_project.Chap90.Definition_90_10_1_Schlessinger
public import stacks_project.Chap90.Definition_90_3_2_SmallExtension

/-!
# Lifting along a small extension after pushforward

In a predeformation category satisfying (S2), a commutative square over
`A1 ×_A A2 → A2` over `A1 → A` with `f2` a small extension and a section `h` of
the cospan lifts along `a2` whenever `x1` maps into a pushforward of `y` along
`g(u, v) = residue(u) ⊕ (v - h(u))`.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- Lemma 90.10.8: let `p : F ⥤ ArtinianLocalAlgCat Λ k` be a predeformation category
satisfying (S2). For a commutative square `CommSq c d a2 a1` in `F` lying over the
cospan pullback square `cospanPullback f1 f2 h hh ⟶ A2` over `A1 ⟶ A`, with `f2` a
small extension and `h ≫ f2 = f1`, if `φ : y ⟶ gy` lifts `cospanPullbackDiff h hh`
and there is a morphism `x1 ⟶ gy`, then there exists `b : x1 ⟶ x2` with
`b ≫ a2 = a1`. -/
@[stacks 06IT]
theorem exists_hom_of_pushforward (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsPredeformationCategory p] [HasSchlessingerS2 p]
    {A A1 A2 : ArtinianLocalAlgCat Λ k}
    (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) [IsSmallExtension f2]
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) {y x1 x2 x : F}
    (c : y ⟶ x2) (d : y ⟶ x1) (a2 : x2 ⟶ x) (a1 : x1 ⟶ x)
    (h_sq : CommSq c d a2 a1)
    (hc : p.IsHomLift (cospanPullbackSnd f1 f2 h hh) c)
    (hd : p.IsHomLift (cospanPullbackFst f1 f2 h hh) d)
    (ha2 : p.IsHomLift f2 a2) (ha1 : p.IsHomLift f1 a1)
    {gy : F} (φ : y ⟶ gy) (hφ : p.IsHomLift (cospanPullbackDiff h hh) φ) :
    Nonempty (x1 ⟶ gy) → ∃ b : x1 ⟶ x2, b ≫ a2 = a1 := sorry

end CategoryTheory.Functor
