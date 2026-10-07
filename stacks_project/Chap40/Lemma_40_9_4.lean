module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.MorphismProperty

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.GroupoidScheme

/- Lemma 40.9.4 (1): if the source map of the first restriction has a
base-change-stable, target-local property, and the original source map has open image
covered by its factorization through that image, then the source map of the composite
restriction has the property. -/
@[stacks 04MX]
#check
  (AlgebraicGeometry.GroupoidScheme.property_compRestriction_of_restriction :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S) {U' U'' : Over S}
      (g : U' ⟶ G.U) (g' : U'' ⟶ U') (τ : DescentTopology)
      (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
      [P.IsLocalAtTarget τ.precoverage] (V : Scheme.Opens G.U.left)
      (hToImage : (Limits.pullback g G.t).left ⟶ V.toScheme),
      Set.range (pullback.snd g G.t ≫ G.s).left.base = (V : Set G.U.left) →
      hToImage ≫ V.ι = (pullback.snd g G.t ≫ G.s).left →
      Presieve.singleton hToImage ∈ τ.precoverage V.toScheme →
      P (pullback.snd g' (G.pullback g).t ≫ (G.pullback g).s).left →
      P (pullback.snd (g' ≫ g) G.t ≫ G.s).left)

/- Lemma 40.9.4 (2): if the original target map is a cover and the source map of the
composite restriction has a base-change-stable, target-local property, then the source
map of the second restriction has the property. -/
@[stacks 04MX]
#check
  (AlgebraicGeometry.GroupoidScheme.property_restriction_of_compRestriction :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S) {U' U'' : Over S}
      (g : U' ⟶ G.U) (g' : U'' ⟶ U') (τ : DescentTopology)
      (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
      [P.IsLocalAtTarget τ.precoverage],
      Presieve.singleton G.t.left ∈ τ.precoverage G.U.left →
      P (pullback.snd (g' ≫ g) G.t ≫ G.s).left →
      P (pullback.snd g' (G.pullback g).t ≫ (G.pullback g).s).left)

end AlgebraicGeometry.GroupoidScheme
