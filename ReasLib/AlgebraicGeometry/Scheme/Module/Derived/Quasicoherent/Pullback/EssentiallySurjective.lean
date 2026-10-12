/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.CohomologicalDimension

/-!
# Essential Surjectivity of Quasicoherent Derived Pullback

Derived restriction along a quasi-compact open immersion is essentially surjective on
complexes with quasicoherent cohomology. The bounded-above and bounded cases additionally
assume that the target scheme is quasi-compact.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh.OpenImmersion

/-- Derived restriction on unbounded complexes with quasicoherent cohomology along a
quasi-compact open immersion is essentially surjective. -/
instance pullbackEssSurj {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] :
    (pullback j).EssSurj := sorry

/-- Derived restriction on bounded-below complexes with quasicoherent cohomology along a
quasi-compact open immersion is essentially surjective. -/
instance pullbackPlusEssSurj {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] :
    (pullbackPlus j).EssSurj := sorry

/-- If the target scheme is quasi-compact, derived restriction on bounded-above complexes
with quasicoherent cohomology along a quasi-compact open immersion is essentially
surjective. -/
instance pullbackMinusEssSurj {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] [CompactSpace X] :
    (pullbackMinus j).EssSurj := sorry

/-- If the target scheme is quasi-compact, derived restriction on bounded complexes with
quasicoherent cohomology along a quasi-compact open immersion is essentially surjective. -/
instance pullbackBoundedEssSurj {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] [CompactSpace X] :
    (pullbackBounded j).EssSurj := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh.OpenImmersion
