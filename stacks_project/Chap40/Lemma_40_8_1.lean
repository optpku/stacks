module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.CohenMacaulayPresentation

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 40.8.1: a flat, locally finitely presented groupoid scheme has an object open
whose endpoint inverse images are the largest Cohen--Macaulay source opens, whose crossed
endpoint restrictions are surjective, and whose restricted groupoid has Cohen--Macaulay,
locally finitely presented source and target maps. -/
@[stacks 0460] #check
  (AlgebraicGeometry.GroupoidScheme.existsCohenMacaulayPresentationOpen :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      [AlgebraicGeometry.Flat G.s.left]
      [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
      [AlgebraicGeometry.Flat G.t.left]
      [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left],
      ∃ W : AlgebraicGeometry.Scheme.Opens G.U.left,
        IsGreatest
            {V : AlgebraicGeometry.Scheme.Opens G.R.left |
              AlgebraicGeometry.CohenMacaulay (V.ι ≫ G.s.left)}
            (G.t.left ⁻¹ᵁ W) ∧
          IsGreatest
            {V : AlgebraicGeometry.Scheme.Opens G.R.left |
              AlgebraicGeometry.CohenMacaulay (V.ι ≫ G.t.left)}
            (G.s.left ⁻¹ᵁ W) ∧
          AlgebraicGeometry.Surjective ((G.s.left ⁻¹ᵁ W).ι ≫ G.t.left) ∧
          AlgebraicGeometry.Surjective ((G.t.left ⁻¹ᵁ W).ι ≫ G.s.left) ∧
          (let U' : Over S := Over.mk (W.ι ≫ G.U.hom)
           let j : U' ⟶ G.U := Over.homMk W.ι
           AlgebraicGeometry.CohenMacaulay (G.pullback j).s.left ∧
             AlgebraicGeometry.LocallyOfFinitePresentation (G.pullback j).s.left ∧
             AlgebraicGeometry.CohenMacaulay (G.pullback j).t.left ∧
             AlgebraicGeometry.LocallyOfFinitePresentation (G.pullback j).t.left))
