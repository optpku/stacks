/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.QuotientSheaf.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/- Lemma 39.20.6 (1): the quotient-sheaf comparison for a restricted groupoid is
injective on sections over every scheme over the base. -/
@[stacks 02VH]
#check (AlgebraicGeometry.GroupoidScheme.pullbackQuotientMap_app_injective :
  ∀ {S : Scheme.{u}} (τ : StandardTopology) (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) (T : Over S),
    Function.Injective
      ((G.toPreRelation.pullbackQuotientMap (τ.overTopology S) g).hom.app (op T)))

/- Lemma 39.20.6 (2): local surjectivity of the saturation morphism makes the
quotient-sheaf comparison an isomorphism. -/
@[stacks 02VH]
#check (AlgebraicGeometry.GroupoidScheme.pullbackQuotientMap_isIso_of_saturationLocallySurjective :
  ∀ {S : Scheme.{u}} (τ : StandardTopology) (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U),
    Sheaf.IsLocallySurjective
      ((τ.overTopology S).uliftSheafifiedRepresentableMap.{u + 1} (G.saturationMap g)) →
    IsIso (G.toPreRelation.pullbackQuotientMap (τ.overTopology S) g))

/- Lemma 39.20.6 (3): a covering saturation morphism makes the quotient-sheaf
comparison an isomorphism. -/
@[stacks 02VH]
#check (AlgebraicGeometry.GroupoidScheme.pullbackQuotientMap_isIso_of_saturationCovering :
  ∀ {S : Scheme.{u}} (τ : StandardTopology) (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U),
    (τ.overTopology S).coveringArrows (G.saturationMap g) →
    IsIso (G.toPreRelation.pullbackQuotientMap (τ.overTopology S) g))

/- Lemma 39.20.6 (4): local surjectivity of the restricting morphism makes the
quotient-sheaf comparison an isomorphism. -/
@[stacks 02VH]
#check (AlgebraicGeometry.GroupoidScheme.pullbackQuotientMap_isIso_of_locallySurjective :
  ∀ {S : Scheme.{u}} (τ : StandardTopology) (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U),
    Sheaf.IsLocallySurjective
      ((τ.overTopology S).uliftSheafifiedRepresentableMap.{u + 1} g) →
    IsIso (G.toPreRelation.pullbackQuotientMap (τ.overTopology S) g))

/- Lemma 39.20.6 (5): a covering restricting morphism makes the quotient-sheaf
comparison an isomorphism. -/
@[stacks 02VH]
#check (AlgebraicGeometry.GroupoidScheme.pullbackQuotientMap_isIso_of_covering :
  ∀ {S : Scheme.{u}} (τ : StandardTopology) (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U),
    (τ.overTopology S).coveringArrows g →
    IsIso (G.toPreRelation.pullbackQuotientMap (τ.overTopology S) g))

end AlgebraicGeometry.GroupoidScheme
