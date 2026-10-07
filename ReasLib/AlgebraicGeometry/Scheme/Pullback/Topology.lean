module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks

/-!
# Underlying topological pullbacks of scheme fibers
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

noncomputable section

universe u

namespace AlgebraicGeometry.IsPreimmersion

variable {P X Y S : Scheme.{u}}
variable {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}

/-- Forgetting a scheme pullback square whose right-hand map is a preimmersion preserves the
pullback square on underlying topological spaces. -/
@[stacks 01K1 "underlying-space pullback along a preimmersion"]
theorem isPullback_toTop_of_right
    (h : IsPullback fst snd f g) [IsPreimmersion g] :
    IsPullback
      (Scheme.forgetToTop.map fst)
      (Scheme.forgetToTop.map snd)
      (Scheme.forgetToTop.map f)
      (Scheme.forgetToTop.map g) := sorry

/-- Forgetting a scheme pullback square whose left-hand map is a preimmersion preserves the
pullback square on underlying topological spaces. -/
@[stacks 01K1 "underlying-space pullback along a preimmersion, left leg"]
theorem isPullback_toTop_of_left
    (h : IsPullback fst snd f g) [IsPreimmersion f] :
    IsPullback
      (Scheme.forgetToTop.map fst)
      (Scheme.forgetToTop.map snd)
      (Scheme.forgetToTop.map f)
      (Scheme.forgetToTop.map g) := sorry

end AlgebraicGeometry.IsPreimmersion

namespace AlgebraicGeometry.Scheme.Pullback

variable {X S : Scheme.{u}}

/-! The two Chapter 26 squares are thin source-facing specializations of the generic
`IsPreimmersion` owner above.  Keeping these named squares makes the exact pullback geometry
available to downstream developments without making them reconstruct the fiber diagrams. -/

/-- 01K1, Lemma 26.18.5 (1): the scheme-theoretic fiber square remains a pullback after passing
to underlying topological spaces. -/
@[stacks 01K1]
theorem fiber_isPullback_toTop (f : X ⟶ S) (s : S) :
    IsPullback
      (Scheme.forgetToTop.map (f.fiberι s))
      (Scheme.forgetToTop.map (f.fiberToSpecResidueField s))
      (Scheme.forgetToTop.map f)
      (Scheme.forgetToTop.map (S.fromSpecResidueField s)) := sorry

/-- 01K1, Lemma 26.18.5 (2): base change along the spectrum of a stalk remains a pullback after
passing to underlying topological spaces. -/
@[stacks 01K1]
theorem fromSpecStalk_isPullback_toTop (f : X ⟶ S) (s : S) :
    IsPullback
      (Scheme.forgetToTop.map (pullback.snd (S.fromSpecStalk s) f))
      (Scheme.forgetToTop.map (pullback.fst (S.fromSpecStalk s) f))
      (Scheme.forgetToTop.map f)
      (Scheme.forgetToTop.map (S.fromSpecStalk s)) := sorry

end AlgebraicGeometry.Scheme.Pullback
