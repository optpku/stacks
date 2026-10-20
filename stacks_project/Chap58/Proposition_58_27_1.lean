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

namespace AlgebraicGeometry.Scheme

/- Proposition 58.27.1 (1): if `X` is proper over a field `k`, `L` is an ample invertible
`𝒪_X`-module, `s` is a global section of `L`, and
`depth(𝒪_{X,x}) + dim(closure {x}) > 1` for every `x` outside the zero scheme `Y = Z(s)`,
then restriction `FÉt_X → FÉt_Y` is fully faithful. -/
@[stacks 0ELC] #check
  (AlgebraicGeometry.Scheme.finiteEtaleBaseChange_fullyFaithful_of_ampleZeroScheme_depth :
    ∀ {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    (L : P.left.Modules) [L.Invertible] [L.IsAmple] (s : L.sections)
    (hdepth : ∀ x : P.left, x ∉ Set.range (zeroSchemeι L s) →
      ((WithTop.map Int.ofNat
          (moduleDepth (SchemeOverField.stalkRing P x)
            (SchemeOverField.stalkRing P x)) : WithTop ℤ) : EInt) +
        WithBot.map (WithTop.map Int.ofNat)
          (topologicalKrullDim (closure ({x} : Set P.left))) >
        (1 : EInt)),
    Nonempty (finiteEtaleBaseChange (zeroSchemeι L s)).FullyFaithful)

/- Proposition 58.27.1 (2): under the same proper/ample/depth hypotheses, restriction
`FÉt_V → FÉt_Y` is fully faithful for every open `V ⊂ X` containing `Y = Z(s)`. -/
@[stacks 0ELC] #check
  (AlgebraicGeometry.Scheme.finiteEtaleBaseChange_fullyFaithful_of_ampleZeroScheme_depth_open :
    ∀ {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    (L : P.left.Modules) [L.Invertible] [L.IsAmple] (s : L.sections)
    (V : P.left.Opens) (hY : Set.range (zeroSchemeι L s) ⊆ (V : Set P.left))
    (hdepth : ∀ x : P.left, x ∉ Set.range (zeroSchemeι L s) →
      ((WithTop.map Int.ofNat
          (moduleDepth (SchemeOverField.stalkRing P x)
            (SchemeOverField.stalkRing P x)) : WithTop ℤ) : EInt) +
        WithBot.map (WithTop.map Int.ofNat)
          (topologicalKrullDim (closure ({x} : Set P.left))) >
        (1 : EInt)),
    Nonempty (finiteEtaleBaseChange (pullback.fst V.ι (zeroSchemeι L s))).FullyFaithful)

end AlgebraicGeometry.Scheme
