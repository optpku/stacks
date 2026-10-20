module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Lefschetz
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/- Proposition 58.27.3: if `X` is proper over a field `k`, `L` is an ample invertible
`𝒪_X`-module, `s` is a global section of `L`, `Y = Z(s)`,
`depth(𝒪_{X,x}) + dim(closure {x}) > 2` for every `x` in `X \ Y`, and purity holds for
`𝒪_{X,x}` at every closed point of `X \ Y`, then restriction `FÉt_X → FÉt_Y` is an
equivalence. -/
@[stacks 0ELE] #check
  (AlgebraicGeometry.Scheme.finiteEtaleBaseChange_isEquivalence_of_ampleZeroScheme_depth_purity :
    ∀ {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    (L : P.left.Modules) [L.Invertible] [L.IsAmple] (s : L.sections)
    [hdepth : Fact (∀ x : P.left, x ∉ Set.range (zeroSchemeι L s) →
      ((WithTop.map Int.ofNat
          (moduleDepth (SchemeOverField.stalkRing P x)
            (SchemeOverField.stalkRing P x)) : WithTop ℤ) : EInt) +
        WithBot.map (WithTop.map Int.ofNat)
          (topologicalKrullDim (closure ({x} : Set P.left))) >
        (2 : EInt))]
    [hpurity : Fact (∀ x : P.left, x ∈ closedPoints P.left →
      x ∉ Set.range (zeroSchemeι L s) →
      PuncturedSpectrum.HasPurity (SchemeOverField.stalkRing P x))],
    Functor.IsEquivalence (finiteEtaleBaseChange (zeroSchemeι L s)))

/- The connectedness consequence of Proposition 58.27.3. -/
#check
  (AlgebraicGeometry.Scheme.connectedSpace_zeroScheme_iff_of_ampleZeroScheme_depth_purity :
    ∀ {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    (L : P.left.Modules) [L.Invertible] [L.IsAmple] (s : L.sections)
    (hdepth : ∀ x : P.left, x ∉ Set.range (zeroSchemeι L s) →
      ((WithTop.map Int.ofNat
          (moduleDepth (SchemeOverField.stalkRing P x)
            (SchemeOverField.stalkRing P x)) : WithTop ℤ) : EInt) +
        WithBot.map (WithTop.map Int.ofNat)
          (topologicalKrullDim (closure ({x} : Set P.left))) >
        (2 : EInt))
    (hpurity : ∀ x : P.left, x ∈ closedPoints P.left →
      x ∉ Set.range (zeroSchemeι L s) →
      PuncturedSpectrum.HasPurity (SchemeOverField.stalkRing P x)),
    ConnectedSpace P.left ↔ ConnectedSpace (zeroScheme L s))

/- The induced map on étale fundamental groups is an isomorphism. -/
#check
  (AlgebraicGeometry.Scheme.etaleFundamentalGroup_isIso_of_ampleZeroScheme_depth_purity :
    ∀ {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    (L : P.left.Modules) [L.Invertible] [L.IsAmple] (s : L.sections)
    (hdepth : ∀ x : P.left, x ∉ Set.range (zeroSchemeι L s) →
      ((WithTop.map Int.ofNat
          (moduleDepth (SchemeOverField.stalkRing P x)
            (SchemeOverField.stalkRing P x)) : WithTop ℤ) : EInt) +
        WithBot.map (WithTop.map Int.ofNat)
          (topologicalKrullDim (closure ({x} : Set P.left))) >
        (2 : EInt))
    (hpurity : ∀ x : P.left, x ∈ closedPoints P.left →
      x ∉ Set.range (zeroSchemeι L s) →
      PuncturedSpectrum.HasPurity (SchemeOverField.stalkRing P x))
    [ConnectedSpace P.left] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (point : Spec (CommRingCat.of Ω) ⟶ zeroScheme L s),
    IsHomeomorph (Hom.fundamentalGroupMap (zeroSchemeι L s) point))

end AlgebraicGeometry.Scheme
