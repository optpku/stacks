/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Coproduct.FiniteComponents
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_16_4_Etale

/-!
# Absolute normalization morphisms of algebraic spaces

An absolute normalization morphism of algebraic spaces is characterized étale
locally: pullback along an étale morphism from a scheme recovers the
scheme-level absolute normalization.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The algebraic space over `S` represented by the absolute normalization of the
underlying scheme of `T`. -/
def ofOverSchemeNormalization {S : Scheme.{u}} (T : Over S)
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens T.left] :
    AlgebraicSpace S :=
  ofOver (Over.mk (T.left.normalizationTo ≫ T.hom))

/-- The morphism of algebraic spaces induced by the scheme-level absolute
normalization of the underlying scheme of `T`. -/
def ofOverSchemeNormalizationTo {S : Scheme.{u}} (T : Over S)
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens T.left] :
    ofOverSchemeNormalization T ⟶ ofOver T :=
  ofOverMap (Over.homMk T.left.normalizationTo rfl)

/-- A morphism `ν : Xν ⟶ X` of algebraic spaces is an absolute normalization
morphism when every étale pullback along a scheme atlas with finitely many
irreducible components on compact opens recovers the scheme-level absolute
normalization. -/
class IsNormalizationTo {S : Scheme.{u}} {Xν X : AlgebraicSpace S} (ν : Xν ⟶ X) :
    Prop where
  /-- Étale pullbacks of `ν` along scheme atlases are the scheme-level absolute
  normalization. -/
  exists_iso : ∀ {U : Over S} (g : ofOver U ⟶ X)
    [Etale g] [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left],
    ∃ e : pullback ν g ≅ ofOverSchemeNormalization U,
      e.hom ≫ ofOverSchemeNormalizationTo U = pullback.snd ν g

/-- A morphism of algebraic spaces is an absolute normalization morphism if every
étale pullback along a scheme atlas with finitely many irreducible components on
compact opens recovers the scheme-level absolute normalization. -/
theorem IsNormalizationTo.of {S : Scheme.{u}} {Xν X : AlgebraicSpace S} {ν : Xν ⟶ X}
    (h : ∀ {U : Over S} (g : ofOver U ⟶ X)
      [Etale g] [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left],
      ∃ e : pullback ν g ≅ ofOverSchemeNormalization U,
        e.hom ≫ ofOverSchemeNormalizationTo U = pullback.snd ν g) :
    IsNormalizationTo ν :=
  sorry

/-- A morphism of algebraic spaces is an absolute normalization morphism if and only
if every étale pullback along a scheme atlas with finitely many irreducible
components on compact opens recovers the scheme-level absolute normalization. -/
theorem isNormalizationTo_iff {S : Scheme.{u}} {Xν X : AlgebraicSpace S}
    (ν : Xν ⟶ X) :
    IsNormalizationTo ν ↔
      ∀ {U : Over S} (g : ofOver U ⟶ X)
        [Etale g] [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left],
        ∃ e : pullback ν g ≅ ofOverSchemeNormalization U,
          e.hom ≫ ofOverSchemeNormalizationTo U = pullback.snd ν g :=
  sorry

/-- An absolute normalization morphism pulls back along étale scheme atlases to the
scheme-level absolute normalization. -/
theorem IsNormalizationTo.spec {S : Scheme.{u}} {Xν X : AlgebraicSpace S}
    (ν : Xν ⟶ X) [IsNormalizationTo ν] {U : Over S} (g : ofOver U ⟶ X)
    [Etale g] [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left] :
    ∃ e : pullback ν g ≅ ofOverSchemeNormalization U,
      e.hom ≫ ofOverSchemeNormalizationTo U = pullback.snd ν g :=
  sorry

/-- The scheme-level absolute normalization of a scheme over `S`, viewed as a
morphism of algebraic spaces, is an absolute normalization morphism. -/
instance instIsNormalizationTo_ofOverSchemeNormalizationTo {S : Scheme.{u}}
    (T : Over S) [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens T.left] :
    IsNormalizationTo (ofOverSchemeNormalizationTo T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
