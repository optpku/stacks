module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap109.Lemma_109_3_1_Family

/-!
# Lemma 109.4.3

A family of curves becomes a scheme, and even H-projective, after an étale
covering of the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The morphism of algebraic spaces over `B` induced by a member of an étale
covering of the scheme `S`. -/
def ofEtaleCoverMap {B : Scheme.{u}} {S : Over B}
    (𝒰 : S.left.Cover.{u} Scheme.etalePrecoverage) (i : 𝒰.I₀) :
    ofOver (Over.mk (𝒰.f i ≫ S.hom)) ⟶ ofOver S :=
  ofOverMap (Over.homMk (𝒰.f i) rfl : Over.mk (𝒰.f i ≫ S.hom) ⟶ S)

/-- `ofEtaleCoverMap 𝒰 i` is `ofOverMap` of the corresponding morphism in
`Over B`. -/
theorem ofEtaleCoverMap_eq {B : Scheme.{u}} {S : Over B}
    (𝒰 : S.left.Cover.{u} Scheme.etalePrecoverage) (i : 𝒰.I₀) :
    ofEtaleCoverMap 𝒰 i =
      ofOverMap (Over.homMk (𝒰.f i) rfl : Over.mk (𝒰.f i ≫ S.hom) ⟶ S) :=
  sorry

/-- The fibre product `X ×_S S_i` of a family along a member of an étale
covering of `S`. -/
abbrev ofEtaleCoverPullback {B : Scheme.{u}} {X : AlgebraicSpace B} {S : Over B}
    (f : X ⟶ ofOver S) (𝒰 : S.left.Cover.{u} Scheme.etalePrecoverage)
    (i : 𝒰.I₀) : AlgebraicSpace B :=
  pullback f (ofEtaleCoverMap 𝒰 i)

/-- The structure morphism of `ofEtaleCoverPullback f 𝒰 i` is the second
projection of the fibre product along `ofEtaleCoverMap 𝒰 i`. -/
theorem ofEtaleCoverPullback_snd {B : Scheme.{u}} {X : AlgebraicSpace B}
    {S : Over B} (f : X ⟶ ofOver S)
    (𝒰 : S.left.Cover.{u} Scheme.etalePrecoverage) (i : 𝒰.I₀) :
    (pullback.snd f (ofEtaleCoverMap 𝒰 i) :
        ofEtaleCoverPullback f 𝒰 i ⟶ ofOver (Over.mk (𝒰.f i ≫ S.hom))) =
      pullback.snd f (ofEtaleCoverMap 𝒰 i) :=
  sorry

/-- Lemma 109.4.3: if `X ⟶ S` is a family of curves, there exists an étale
covering `{S_i ⟶ S}` such that each `X_i = X ×_S S_i` is a scheme. We may
even assume `X_i` is H-projective over `S_i`. -/
@[stacks 0E6F]
theorem exists_etaleCovering_hProjective {B : Scheme.{u}} {X : AlgebraicSpace B}
    {S : Over B} (f : X ⟶ ofOver S) [IsFamily f] :
    ∃ 𝒰 : S.left.Cover.{u} Scheme.etalePrecoverage, ∀ i : 𝒰.I₀,
      IsScheme (ofEtaleCoverPullback f 𝒰 i) ∧
        ∃ (Y : Scheme.{u}) (π : Y ⟶ 𝒰.X i)
          (e : ofEtaleCoverPullback f 𝒰 i ≅
            ofOver (Over.mk (π ≫ 𝒰.f i ≫ S.hom))),
          HProjective π ∧
            e.hom ≫ ofOverHomMk π rfl =
              pullback.snd f (ofEtaleCoverMap 𝒰 i) :=
  sorry

/-- If `X ⟶ S` is a family of curves, there exists an étale covering
`{S_i ⟶ S}` such that each fibre product `X ×_S S_i` is a scheme. -/
theorem exists_etaleCovering_isScheme {B : Scheme.{u}} {X : AlgebraicSpace B}
    {S : Over B} (f : X ⟶ ofOver S) [IsFamily f] :
    ∃ 𝒰 : S.left.Cover.{u} Scheme.etalePrecoverage, ∀ i : 𝒰.I₀,
      IsScheme (ofEtaleCoverPullback f 𝒰 i) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
