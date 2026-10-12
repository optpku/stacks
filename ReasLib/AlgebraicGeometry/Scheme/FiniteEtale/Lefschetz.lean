/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Order.WithBotTop
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Purity
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.TopologicalInvariance
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.ZeroScheme
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Noetherian
public import ReasLib.RingTheory.Depth
public import ReasLib.Topology.KrullDimension.Local

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- Finite étale restriction to the zero scheme of an ample section is fully faithful under the
properness and local depth-dimension condition. -/
theorem finiteEtaleBaseChange_fullyFaithful_of_ampleZeroScheme_depth
    {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    (L : P.left.Modules) [L.Invertible] [L.IsAmple] (s : L.sections)
    (hdepth : ∀ x : P.left, x ∉ Set.range (zeroSchemeι L s) →
      ((WithTop.map Int.ofNat
          (moduleDepth (SchemeOverField.stalkRing P x)
            (SchemeOverField.stalkRing P x)) : WithTop ℤ) : EInt) +
        WithBot.map (WithTop.map Int.ofNat)
          (topologicalKrullDim (closure ({x} : Set P.left))) >
        (1 : EInt)) :
    Nonempty (finiteEtaleBaseChange (zeroSchemeι L s)).FullyFaithful := sorry

/-- Finite étale restriction from any open neighborhood of the zero scheme of an ample section is
fully faithful under the properness and local depth-dimension condition. -/
theorem finiteEtaleBaseChange_fullyFaithful_of_ampleZeroScheme_depth_open
    {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    (L : P.left.Modules) [L.Invertible] [L.IsAmple] (s : L.sections)
    (V : P.left.Opens) (hY : Set.range (zeroSchemeι L s) ⊆ (V : Set P.left))
    (hdepth : ∀ x : P.left, x ∉ Set.range (zeroSchemeι L s) →
      ((WithTop.map Int.ofNat
          (moduleDepth (SchemeOverField.stalkRing P x)
            (SchemeOverField.stalkRing P x)) : WithTop ℤ) : EInt) +
        WithBot.map (WithTop.map Int.ofNat)
          (topologicalKrullDim (closure ({x} : Set P.left))) >
        (1 : EInt)) :
    Nonempty (finiteEtaleBaseChange (pullback.fst V.ι (zeroSchemeι L s))).FullyFaithful := sorry

namespace finiteEtaleNeighborhoodRestriction

/-- For a proper scheme over a field and an ample invertible module with a global section,
restriction from the colimit of finite étale categories on open neighborhoods of its zero scheme
to the finite étale category of that zero scheme is an equivalence whenever the sum of stalk
depth and point-closure dimension exceeds two outside the zero scheme. -/
theorem isEquivalence_of_ampleZeroScheme_depth
    {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    (L : P.left.Modules) [L.Invertible] [L.IsAmple] (s : L.sections)
    (hdepth : ∀ x : P.left, x ∉ Set.range (zeroSchemeι L s) →
      ((WithTop.map Int.ofNat (moduleDepth (SchemeOverField.stalkRing P x)
        (SchemeOverField.stalkRing P x)) : WithTop ℤ) : WithBot (WithTop ℤ)) +
        WithBot.map (WithTop.map Int.ofNat)
          (topologicalKrullDim (closure ({x} : Set P.left))) > (2 : EInt))
    (t : ColimitCocone (finiteEtaleNeighborhoodDiagram (zeroIdealSheaf L s))) :
    Functor.IsEquivalence (finiteEtaleNeighborhoodRestriction (zeroIdealSheaf L s) t) := sorry

end finiteEtaleNeighborhoodRestriction

/-- The restriction functor on finite étale schemes over the zero scheme of an ample section is
an equivalence under the properness, depth-dimension, and local purity hypotheses. -/
instance finiteEtaleBaseChange_isEquivalence_of_ampleZeroScheme_depth_purity
    {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
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
      PuncturedSpectrum.HasPurity (SchemeOverField.stalkRing P x))] :
    Functor.IsEquivalence (finiteEtaleBaseChange (zeroSchemeι L s)) := sorry

/-- Under the properness, depth-dimension, and local purity hypotheses, the zero scheme of an
ample section is connected exactly when the ambient scheme is connected. -/
theorem connectedSpace_zeroScheme_iff_of_ampleZeroScheme_depth_purity
    {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
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
      PuncturedSpectrum.HasPurity (SchemeOverField.stalkRing P x)) :
    ConnectedSpace P.left ↔ ConnectedSpace (zeroScheme L s) := sorry

/-- For a connected proper scheme over a field, an ample invertible module, and a global section,
assume that the sum of stalk depth and point-closure dimension exceeds two outside the zero scheme
and that purity holds at every closed point outside it. Then the zero-scheme inclusion induces a
homeomorphism on étale fundamental groups at every algebraically closed geometric basepoint. -/
theorem etaleFundamentalGroup_isIso_of_ampleZeroScheme_depth_purity
    {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
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
    (point : Spec (CommRingCat.of Ω) ⟶ zeroScheme L s) :
    IsHomeomorph (Hom.fundamentalGroupMap (zeroSchemeι L s) point) := sorry

end AlgebraicGeometry.Scheme
