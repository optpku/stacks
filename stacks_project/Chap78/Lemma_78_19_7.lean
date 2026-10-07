module

public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import stacks_project.Chap73.Definition_73_7_1_FppfCover
public import stacks_project.Chap73.Lemma_73_7_5
public import stacks_project.Chap78.Lemma_78_11_2_Groupoid
public import stacks_project.Chap78.Lemma_78_19_6_QuotientMap
public import stacks_project.Chap78.Lemma_78_19_7_Saturation

/-!
# Lemma 78.19.7

Restriction of a groupoid in algebraic spaces along a morphism of algebraic spaces
over the base induces an injective map of fppf quotient sheaves, which is an
isomorphism when the associated saturation morphism is surjective as a map of sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.PreRelation

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Lemma 78.19.7 (1): let `(U, R, s, t, c)` be a groupoid in algebraic spaces over `B`
and let `g : U' ⟶ U` be a morphism over `B`. Writing `(U', R', s', t', c')` for the
restriction of the groupoid to `U'`, identified with `G.toPreRelation.restrict g`,
the induced map of fppf quotient sheaves `U'/R' ⟶ U/R` is injective as a map of
sheaves. -/
@[stacks 044N]
theorem quotientSheafMap_isLocallyInjective {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    Sheaf.IsLocallyInjective (G.toPreRelation.quotientSheafMap g) :=
  sorry

/-- Lemma 78.19.7 (2): if the saturation morphism
`h = s ∘ pr₁ : U' ×_{g, U, t} R ⟶ U` is a surjection of fppf sheaves, then the
restriction-induced map `U'/R' ⟶ U/R` is an isomorphism of sheaves. -/
@[stacks 044N]
theorem quotientSheafMap_isIso_of_saturationLocallySurjective {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) {U' : Over B}
    (g : U' ⟶ G.U)
    (h_saturation : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (G.saturationMap g).left) :
    IsIso (G.toPreRelation.quotientSheafMap g) :=
  sorry

/-- Lemma 78.19.7 (3): if `{h : U' ×_{g, U, t} R ⟶ U}` is an fppf covering, then
the restriction-induced map `U'/R' ⟶ U/R` is an isomorphism of sheaves. -/
@[stacks 044N]
theorem quotientSheafMap_isIso_of_saturationCovering {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) {U' : Over B}
    (g : U' ⟶ G.U)
    [FppfCovering (fun _ : PUnit ↦ (Limits.pullback g G.t).left)
      (fun _ ↦ (G.saturationMap g).left)] :
    IsIso (G.toPreRelation.quotientSheafMap g) :=
  sorry

/-- Lemma 78.19.7 (4): if `U' ⟶ U` is a surjection of fppf sheaves, then the
restriction-induced map `U'/R' ⟶ U/R` is an isomorphism of sheaves. -/
@[stacks 044N]
theorem quotientSheafMap_isIso_of_locallySurjective {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) {U' : Over B}
    (g : U' ⟶ G.U)
    (hg : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) g.left) :
    IsIso (G.toPreRelation.quotientSheafMap g) :=
  sorry

/-- Lemma 78.19.7 (5): if `{g : U' ⟶ U}` is an fppf covering, then the
restriction-induced map `U'/R' ⟶ U/R` is an isomorphism of sheaves. -/
@[stacks 044N]
theorem quotientSheafMap_isIso_of_fppfCovering {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) {U' : Over B}
    (g : U' ⟶ G.U)
    [FppfCovering (fun _ : PUnit ↦ U'.left) (fun _ ↦ g.left)] :
    IsIso (G.toPreRelation.quotientSheafMap g) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
