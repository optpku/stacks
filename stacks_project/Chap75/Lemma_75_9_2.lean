/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ElementaryDistinguishedSquare.Stability
import StacksCheckRecall

/-!
# Stability of elementary distinguished squares

Elementary distinguished squares of algebraic spaces are stable under shrinking
to open subspaces, under pullback along a morphism of algebraic spaces, and
under base change along a morphism of schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 75.9.2 (1). If `V' ⊂ V` and `U ⊂ U' ⊂ W` are open subspaces and
`W' = U' ∪ f(V')`, then `(U' ⊂ W', f' : V' ⟶ W')` is an elementary distinguished
square. -/
@[stacks 08GN] #check
  (AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare.restrict :
    ∀ {S : Scheme.{u}} {U V W U' V' W' : AlgebraicSpace S}
    {j : U ⟶ W} {f : V ⟶ W} [IsElementaryDistinguishedSquare j f]
    (jW' : U' ⟶ W) (iV' : V' ⟶ V) (iW' : W' ⟶ W) (j' : U' ⟶ W') (f' : V' ⟶ W')
    [IsOpenImmersion jW'] [IsOpenImmersion iV'] [IsOpenImmersion iW']
    (hU : ∃ k : U ⟶ U', k ≫ jW' = j)
    (hW' : Set.range (Points.map iW') =
      Set.range (Points.map jW') ∪ Set.range (Points.map (iV' ≫ f)))
    (hj' : j' ≫ iW' = jW') (hf' : f' ≫ iW' = iV' ≫ f),
    IsElementaryDistinguishedSquare j' f')

/- Lemma 75.9.2 (2). If `p : W' ⟶ W` is a morphism of algebraic spaces, then
`(p⁻¹(U) ⊂ W', V ×_W W' ⟶ W')` is an elementary distinguished square. -/
@[stacks 08GN] #check
  (AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare.pullback :
    ∀ {S : Scheme.{u}} {U V W W' : AlgebraicSpace S}
    (j : U ⟶ W) (f : V ⟶ W) (p : W' ⟶ W)
    [IsElementaryDistinguishedSquare j f],
    IsElementaryDistinguishedSquare (Limits.pullback.snd j p)
      (Limits.pullback.snd f p))

/- Lemma 75.9.2 (3). If `S' ⟶ S` is a morphism of schemes, then
`(S' ×_S U ⊂ S' ×_S W, S' ×_S V ⟶ S' ×_S W)` is an elementary distinguished
square. -/
@[stacks 08GN] #check
  (AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare.baseChange :
    ∀ {S S' : Scheme.{u}} (g : S' ⟶ S) {U V W : AlgebraicSpace S}
    (j : U ⟶ W) (f : V ⟶ W) [IsElementaryDistinguishedSquare j f],
    IsElementaryDistinguishedSquare (baseChangeMap g j) (baseChangeMap g f))
