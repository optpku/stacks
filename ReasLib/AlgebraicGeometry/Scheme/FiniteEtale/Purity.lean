module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Purity
public import ReasLib.RingTheory.Depth
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped ENat

universe u

namespace AlgebraicGeometry.Scheme

/-- Restriction of finite étale schemes along an open immersion of Noetherian
schemes is essentially surjective when every complementary stalk is pure. -/
theorem finiteEtaleBaseChangeEssSurjOfPurity
    {U X : Scheme.{u}} (j : U ⟶ X)
    [IsNoetherian U] [IsNoetherian X] [IsOpenImmersion j]
    (h_purity : ∀ x : X, x ∉ Set.range j.base →
      PuncturedSpectrum.HasPurity (X.presheaf.stalk x)) :
    (finiteEtaleBaseChange j).EssSurj := sorry

/-- The purity hypothesis makes essential surjectivity available through the
canonical `Fact` interface for the complementary stalks. -/
instance finiteEtaleBaseChangeEssSurjOfPurityFact
    {U X : Scheme.{u}} (j : U ⟶ X)
    [IsNoetherian U] [IsNoetherian X] [IsOpenImmersion j]
    [Fact (∀ x : X, x ∉ Set.range j.base →
      PuncturedSpectrum.HasPurity (X.presheaf.stalk x))] :
    (finiteEtaleBaseChange j).EssSurj := sorry

/-- For a smooth morphism to a Noetherian scheme, restriction to an open subscheme
is an equivalence on finite étale schemes if the open contains every fiber over
a point whose local ring has depth at most one and is dense in every fiber. -/
theorem finiteEtaleBaseChange_isEquivalence_of_smoothNoetherianFiberDensity
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [IsNoetherian S] (U : X.Opens)
    (h_eq : ∀ s : S,
      moduleDepth (S.presheaf.stalk s) (S.presheaf.stalk s) ≤ (1 : ℕ∞) →
        f.fiberι s ⁻¹ᵁ U = ⊤)
    (h_dense : ∀ s : S, Dense (f.fiberι s ⁻¹ᵁ U : Set (f.fiber s))) :
    Functor.IsEquivalence (finiteEtaleBaseChange U.ι) := sorry

end AlgebraicGeometry.Scheme
