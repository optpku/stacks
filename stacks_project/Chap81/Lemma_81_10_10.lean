module

public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Basic
public import stacks_project.Chap81.Lemma_81_10_10_SupportedOn
public import stacks_project.Chap81.Lemma_81_10_10_Functors

/-!
# Lemma 81.10.10

In Situation 81.10.6, derived pushforward along `f` induces an equivalence
between `D_{QCoh, |f⁻¹Z|}(𝒪_Y)` and `D_{QCoh, |Z|}(𝒪_X)` whose quasi-inverse
is derived pullback.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace DerivedQCoh.SupportedOn

/-- Lemma 81.10.10 (1): In Situation 81.10.6 the functor `Rf_*` induces an
equivalence between `SupportedOn Y (pointsImage (inverseImageι f i))` and
`SupportedOn X (pointsImage i)`. -/
@[stacks 0AFJ, instance]
instance pushforward_isEquivalence {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    (pushforward f i).IsEquivalence :=
  sorry

/-- Lemma 81.10.10 (2): In Situation 81.10.6 the quasi-inverse of this restricted
`Rf_*` equivalence is given by `Lf^*`. -/
@[stacks 0AFJ]
theorem pullback_isQuasiInverse {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    (pushforward f i).IsQuasiInverse (pullback f i) :=
  sorry

end DerivedQCoh.SupportedOn
end AlgebraicGeometry.AlgebraicSpace
