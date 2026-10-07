module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Pullback.Hom
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Functoriality
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.LocalSurjectivity
public import ReasLib.CategoryTheory.Sites.MorphismProperty.Covering
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable

/-!
# Quotient sheaves of pulled-back scheme pre-relations

This module constructs the quotient-sheaf map induced by pulling back a scheme pre-relation
and records its behavior on quotient classes, injectivity, and isomorphism criteria.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- The quotient-sheaf map induced by the canonical morphism from a pulled-back
pre-relation to the original pre-relation. -/
noncomputable abbrev pullbackQuotientMap {S : Scheme.{u}} {U U' : Over S}
    (J : GrothendieckTopology (Over S)) (P : PreRelation U) (g : U' ⟶ U) :
    (P.pullback g).quotientSheaf J ⟶ P.quotientSheaf J :=
  (P.pullbackHom g).quotientSheafMap J

/-- The pullback quotient-sheaf map sends the class represented by `a` to the class
represented by `a ≫ g`. -/
theorem pullbackQuotientMap_quotientClass {S : Scheme.{u}} {U U' T : Over S}
    (J : GrothendieckTopology (Over S)) (P : PreRelation U) (g : U' ⟶ U)
    (a : T ⟶ U') :
    (P.pullbackQuotientMap J g).hom.app (op T)
        ((P.pullback g).quotientClass J a) =
      P.quotientClass J (a ≫ g) := sorry

/-- The quotient projections commute with the quotient-sheaf map induced by pullback. -/
theorem quotientMap_comp_pullbackQuotientMap {S : Scheme.{u}} {U U' : Over S}
    (J : GrothendieckTopology (Over S)) [J.Subcanonical]
    (P : PreRelation U) (g : U' ⟶ U) :
    (P.pullback g).quotientMap J ≫ P.pullbackQuotientMap J g =
      J.uliftYoneda.{u + 1}.map g ≫ P.quotientMap J := by
  simpa [pullbackQuotientMap] using
    (show (P.pullback g).quotientMap J ≫ (P.pullbackHom g).quotientSheafMap J =
        J.uliftYoneda.{u + 1}.map g ≫ P.quotientMap J from by
      simpa [(P.pullbackHom_spec g).1] using
        (P.pullbackHom g).quotientMap_naturality J)

/-- For a standard topology, pulling back a pre-equivalence relation induces an injective
map on quotient-sheaf sections over every scheme over the base. -/
theorem pullbackQuotientMap_app_injective {S : Scheme.{u}} (τ : StandardTopology)
    {U U' : Over S} (P : PreRelation U) (hP : P.IsPreEquivalence)
    (g : U' ⟶ U) (T : Over S) :
    Function.Injective
      ((P.pullbackQuotientMap (τ.overTopology S) g).hom.app (op T)) := sorry

/-- If the sheafified representable map of `g` is locally surjective, then the
quotient-sheaf map induced by pulling back a pre-equivalence relation along `g` is an
isomorphism. -/
theorem pullbackQuotientMap_isIso_of_locallySurjective {S : Scheme.{u}}
    (τ : StandardTopology) {U U' : Over S} (P : PreRelation U)
    (hP : P.IsPreEquivalence) (g : U' ⟶ U)
    (hg : Sheaf.IsLocallySurjective
      ((τ.overTopology S).uliftSheafifiedRepresentableMap.{u + 1} g)) :
    IsIso (P.pullbackQuotientMap (τ.overTopology S) g) := sorry

/-- If `g` is a covering arrow for a standard topology, then the quotient-sheaf map
induced by pulling back a pre-equivalence relation along `g` is an isomorphism. -/
theorem pullbackQuotientMap_isIso_of_covering {S : Scheme.{u}} (τ : StandardTopology)
    {U U' : Over S} (P : PreRelation U) (hP : P.IsPreEquivalence)
    (g : U' ⟶ U) (hg : (τ.overTopology S).coveringArrows g) :
    IsIso (P.pullbackQuotientMap (τ.overTopology S) g) := sorry

end AlgebraicGeometry.Scheme.PreRelation
