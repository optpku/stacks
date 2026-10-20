module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_2_Comparison

/-!
# Open-quotient étale atlases on points of an algebraic space

The topology on the points of an algebraic space is presented by a scheme with a
surjective étale morphism whose induced map of underlying spaces is an open quotient.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Points

-- Preserve the old named argument while reusing the canonical theorem.
attribute [deprecated_arg u point (since := "2026-10-07")] mapOfOver_apply

/-- An étale locally-surjective atlas from a scheme whose induced map on points is an open
quotient map onto `|X|` equipped with the topology `τ`. -/
structure OpenQuotientAtlas {S : Scheme.{u}} (X : AlgebraicSpace S)
    (τ : TopologicalSpace (Points X)) where
  /-- The source scheme over `S`. -/
  U : Over S
  /-- The atlas morphism `ofOver U ⟶ X`. -/
  p : ofOver U ⟶ X
  /-- The atlas morphism is representable and étale. -/
  presheaf_etale : (MorphismProperty.over (@Etale)).presheaf p
  /-- The atlas morphism is étale-locally surjective. -/
  locallySurjective : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p
  /-- The induced map on points is an open quotient map onto `|X|` with topology `τ`. -/
  isOpenQuotientMap :
    @IsOpenQuotientMap U.left (Points X) (inferInstance : TopologicalSpace U.left) τ
      (mapOfOver p)

namespace OpenQuotientAtlas

/-- Reconstruct an open-quotient atlas from a scheme, an étale locally-surjective morphism,
and the open-quotient condition on the induced map of points. -/
def of {S : Scheme.{u}} {X : AlgebraicSpace S} (τ : TopologicalSpace (Points X))
    (U : Over S) (p : ofOver U ⟶ X)
    (presheaf_etale : (MorphismProperty.over (@Etale)).presheaf p)
    (locallySurjective : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p)
    (isOpenQuotientMap :
      @IsOpenQuotientMap U.left (Points X) (inferInstance : TopologicalSpace U.left) τ
        (mapOfOver p)) :
    OpenQuotientAtlas X τ where
  U := U
  p := p
  presheaf_etale := presheaf_etale
  locallySurjective := locallySurjective
  isOpenQuotientMap := isOpenQuotientMap

/-- The identity atlas of a scheme over `S`, viewed as an algebraic space, with the topology
coinduced along `ofOver.pointsEquiv`. -/
def ofOver {S : Scheme.{u}} (U : Over S) :
    OpenQuotientAtlas (AlgebraicSpace.ofOver U)
      (TopologicalSpace.coinduced (fun u ↦ AlgebraicSpace.ofOver.pointsEquiv U u)
        (inferInstance : TopologicalSpace U.left)) where
  U := U
  p := 𝟙 (AlgebraicSpace.ofOver U)
  presheaf_etale := sorry
  locallySurjective := sorry
  isOpenQuotientMap := sorry

/-- An open-quotient atlas is representable étale, étale-locally surjective, and induces an
open quotient map on points. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {τ : TopologicalSpace (Points X)}
    (A : OpenQuotientAtlas X τ) :
    (MorphismProperty.over (@Etale)).presheaf A.p ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) A.p ∧
        @IsOpenQuotientMap A.U.left (Points X)
          (inferInstance : TopologicalSpace A.U.left) τ (mapOfOver A.p) :=
  sorry

end OpenQuotientAtlas

end AlgebraicGeometry.AlgebraicSpace.Points

