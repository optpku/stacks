/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.PreRelation
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Pullback

/-!
# Quotient sheaves of restricted groupoid schemes

This module relates the quotient sheaf of a groupoid scheme to that of its restriction
along a morphism into its object scheme.
-/

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The saturation morphism sends a pair consisting of an object over `U'` and an arrow
targeting its image to the source of that arrow. -/
def saturationMap {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) : Limits.pullback g G.t ⟶ G.U :=
  Limits.pullback.snd g G.t ≫ G.s

/-- The saturation morphism is the source map after the second pullback projection. -/
theorem saturationMap_def {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) :
    G.saturationMap g = Limits.pullback.snd g G.t ≫ G.s := rfl

/-- Local surjectivity of the saturation morphism induces local surjectivity of the
canonical comparison between the quotient sheaves of a groupoid and its restriction. -/
theorem pullbackQuotientMap_locallySurjective_of_saturation {S : Scheme.{u}}
    (τ : StandardTopology) (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.U)
    (h_saturation : Sheaf.IsLocallySurjective
      ((τ.overTopology S).uliftSheafifiedRepresentableMap.{u + 1} (G.saturationMap g))) :
    Sheaf.IsLocallySurjective
      (G.toPreRelation.pullbackQuotientMap (τ.overTopology S) g) := sorry

/-- Pullback along a morphism into the object scheme of a groupoid induces an injective
map on quotient-sheaf sections over every scheme over the base. -/
theorem pullbackQuotientMap_app_injective {S : Scheme.{u}} (τ : StandardTopology)
    (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.U) (T : Over S) :
    Function.Injective
      ((G.toPreRelation.pullbackQuotientMap (τ.overTopology S) g).hom.app (op T)) :=
  Scheme.PreRelation.pullbackQuotientMap_app_injective τ G.toPreRelation
    G.toPreRelation_isPreEquivalence g T

/-- If the saturation morphism induces a locally surjective map of sheaves, then the
quotient-sheaf comparison for the restricted groupoid is an isomorphism. -/
theorem pullbackQuotientMap_isIso_of_saturationLocallySurjective {S : Scheme.{u}}
    (τ : StandardTopology) (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.U)
    (h_saturation : Sheaf.IsLocallySurjective
      ((τ.overTopology S).uliftSheafifiedRepresentableMap.{u + 1} (G.saturationMap g))) :
    IsIso (G.toPreRelation.pullbackQuotientMap (τ.overTopology S) g) := sorry

/-- If the saturation morphism is a covering arrow, then the quotient-sheaf comparison
for the restricted groupoid is an isomorphism. -/
theorem pullbackQuotientMap_isIso_of_saturationCovering {S : Scheme.{u}}
    (τ : StandardTopology) (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.U)
    (h_saturation : (τ.overTopology S).coveringArrows (G.saturationMap g)) :
    IsIso (G.toPreRelation.pullbackQuotientMap (τ.overTopology S) g) := sorry

/-- If a morphism into the object scheme induces a locally surjective map of sheaves,
then the quotient-sheaf comparison for the restricted groupoid is an isomorphism. -/
theorem pullbackQuotientMap_isIso_of_locallySurjective {S : Scheme.{u}}
    (τ : StandardTopology) (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.U)
    (hg : Sheaf.IsLocallySurjective
      ((τ.overTopology S).uliftSheafifiedRepresentableMap.{u + 1} g)) :
    IsIso (G.toPreRelation.pullbackQuotientMap (τ.overTopology S) g) :=
  Scheme.PreRelation.pullbackQuotientMap_isIso_of_locallySurjective τ G.toPreRelation
    G.toPreRelation_isPreEquivalence g hg

/-- If a morphism into the object scheme is a covering arrow, then the quotient-sheaf
comparison for the restricted groupoid is an isomorphism. -/
theorem pullbackQuotientMap_isIso_of_covering {S : Scheme.{u}} (τ : StandardTopology)
    (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.U)
    (hg : (τ.overTopology S).coveringArrows g) :
    IsIso (G.toPreRelation.pullbackQuotientMap (τ.overTopology S) g) :=
  Scheme.PreRelation.pullbackQuotientMap_isIso_of_covering τ G.toPreRelation
    G.toPreRelation_isPreEquivalence g hg

end AlgebraicGeometry.GroupoidScheme
