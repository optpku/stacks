module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/- Lemma 39.20.5 (1): restriction along `g : U' ⟶ U` induces an injective map from
the quotient sheaf of `P.pullback g` to the quotient sheaf of `P`. -/
@[stacks 045Z]
#check (AlgebraicGeometry.Scheme.PreRelation.pullbackQuotientMap_app_injective :
  ∀ {S : Scheme.{u}} (τ : StandardTopology) {U U' : Over S}
    (P : PreRelation U), P.IsPreEquivalence → ∀ (g : U' ⟶ U) (T : Over S),
    Function.Injective
      ((P.pullbackQuotientMap (τ.overTopology S) g).hom.app (op T)))

/- Lemma 39.20.5 (2): if the represented-sheaf map induced by `g : U' ⟶ U` is
locally surjective, then the induced map of quotient sheaves is an isomorphism. -/
@[stacks 045Z]
#check (AlgebraicGeometry.Scheme.PreRelation.pullbackQuotientMap_isIso_of_locallySurjective :
  ∀ {S : Scheme.{u}} (τ : StandardTopology) {U U' : Over S}
    (P : PreRelation U), P.IsPreEquivalence → ∀ (g : U' ⟶ U),
    Sheaf.IsLocallySurjective
      ((τ.overTopology S).uliftSheafifiedRepresentableMap.{u + 1} g) →
    IsIso (P.pullbackQuotientMap (τ.overTopology S) g))

/- Lemma 39.20.5 (3): if `g : U' ⟶ U` is a covering arrow for `τ`, then the induced
map of quotient sheaves is an isomorphism. -/
@[stacks 045Z]
#check (AlgebraicGeometry.Scheme.PreRelation.pullbackQuotientMap_isIso_of_covering :
  ∀ {S : Scheme.{u}} (τ : StandardTopology) {U U' : Over S}
    (P : PreRelation U), P.IsPreEquivalence → ∀ (g : U' ⟶ U),
    (τ.overTopology S).coveringArrows g →
    IsIso (P.pullbackQuotientMap (τ.overTopology S) g))

end AlgebraicGeometry.Scheme.PreRelation
