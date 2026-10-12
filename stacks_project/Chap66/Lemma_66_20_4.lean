/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_20_3_EtaleSupport
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology

/-!
# Support of local sections of an abelian sheaf on `X_étale`

The support of a local section is closed in `|U|`, cannot grow under addition or
sheaf maps, and assembles the support of the sheaf as the union of images in `|X|`.
Surjective maps reverse-include supports; injective maps include them.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 66.20.4 (1): the support of `σ ∈ F(U)` is closed in `|X|`. Formalized as closedness
of the support in `|U|`, the space in which the support of a local section is defined. -/
@[stacks 04KB]
theorem isClosed_abelianSheafSectionSupport {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : smallEtaleSite X) (σ : F.obj.obj (op U)) :
    IsClosed (abelianSheafSectionSupport F U σ : Set U.left.left) :=
  sorry

/-- Lemma 66.20.4 (2): the support of `σ + σ'` is contained in the union of the supports of
`σ, σ' ∈ F(X)`. Formalized for two sections of the same `F(U)`. -/
@[stacks 04KB]
theorem abelianSheafSectionSupport_add_subset {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : smallEtaleSite X) (σ σ' : F.obj.obj (op U)) :
    (abelianSheafSectionSupport F U (σ + σ') : Set U.left.left) ⊆
      (abelianSheafSectionSupport F U σ : Set U.left.left) ∪
        (abelianSheafSectionSupport F U σ' : Set U.left.left) :=
  sorry

/-- Lemma 66.20.4 (3): if `φ : F ⟶ G` is a map of abelian sheaves on `X_étale`, then the
support of `φ(σ)` is contained in the support of `σ ∈ F(U)`. -/
@[stacks 04KB]
theorem abelianSheafSectionSupport_map_subset {S : Scheme.{u}} {X : AlgebraicSpace S}
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (U : smallEtaleSite X) (σ : F.obj.obj (op U)) :
    (abelianSheafSectionSupport G U (φ.hom.app (op U) σ) : Set U.left.left) ⊆
      (abelianSheafSectionSupport F U σ : Set U.left.left) :=
  sorry

/-- Lemma 66.20.4 (4): the support of `F` is the union of the images of the supports of all
local sections of `F`. -/
@[stacks 04KB]
theorem abelianSheafSupport_eq_iUnion_sectionSupport {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    abelianSheafSupport F =
      ⋃ (U : smallEtaleSite X) (σ : F.obj.obj (op U)),
        Points.mapOfOver U.hom '' (abelianSheafSectionSupport F U σ : Set U.left.left) :=
  sorry

/-- Lemma 66.20.4 (5): if `F ⟶ G` is surjective then the support of `G` is a subset of the
support of `F`. -/
@[stacks 04KB]
theorem abelianSheafSupport_subset_of_epi {S : Scheme.{u}} {X : AlgebraicSpace S}
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) [Epi φ] :
    abelianSheafSupport G ⊆ abelianSheafSupport F :=
  sorry

/-- Lemma 66.20.4 (6): if `F ⟶ G` is injective then the support of `F` is a subset of the
support of `G`. -/
@[stacks 04KB]
theorem abelianSheafSupport_subset_of_mono {S : Scheme.{u}} {X : AlgebraicSpace S}
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) [Mono φ] :
    abelianSheafSupport F ⊆ abelianSheafSupport G :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

end
