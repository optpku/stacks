/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Lefschetz
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.finiteEtaleNeighborhoodRestriction

/- Proposition 58.27.2: if `X` is proper over a field `k`, `L` is an ample invertible
`𝒪_X`-module, `s` is a global section of `L`, `Y = Z(s)` is the zero scheme of `s`,
and `𝒱` is the reverse-inclusion poset of open subschemes of `X` containing `Y`,
and if `depth(𝒪_{X,x}) + dim(closure {x}) > 2` for every `x` in `X \ Y`, then the
restriction functor `colim_𝒱 FÉt_V ⟶ FÉt_Y` is an equivalence. -/
@[stacks 0ELD] #check
  (AlgebraicGeometry.Scheme.finiteEtaleNeighborhoodRestriction.isEquivalence_of_ampleZeroScheme_depth :
    ∀ {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    (L : P.left.Modules) [L.Invertible] [L.IsAmple] (s : L.sections)
    (hdepth : ∀ x : P.left, x ∉ Set.range (zeroSchemeι L s) →
      ((WithTop.map Int.ofNat (moduleDepth (SchemeOverField.stalkRing P x)
        (SchemeOverField.stalkRing P x)) : WithTop ℤ) : WithBot (WithTop ℤ)) +
        WithBot.map (WithTop.map Int.ofNat)
          (topologicalKrullDim (closure ({x} : Set P.left))) > (2 : EInt))
    (t : ColimitCocone (finiteEtaleNeighborhoodDiagram (zeroIdealSheaf L s))),
    Functor.IsEquivalence (finiteEtaleNeighborhoodRestriction (zeroIdealSheaf L s) t))

end AlgebraicGeometry.Scheme.finiteEtaleNeighborhoodRestriction
