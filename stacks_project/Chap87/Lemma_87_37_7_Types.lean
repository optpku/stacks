/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Topology.Adic.Complete
public import stacks_project.Chap87.Lemma_87_37_6_CountablyIndexed

/-!
# Locally countably indexed and locally adic* formal algebraic spaces

Functor-of-points locally countably indexed and locally adic* types, with
étale atlases on the carrier `(Over S)ᵒᵖ ⥤ Type u` from
`Definition_88_21_1_Formal`. Affine countably indexed charts reuse
`AffineFormalAlgebraicSpace.IsCountablyIndexedAffine`. Affine adic* charts are
presented by an adic ring with a finitely generated ideal of definition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- An affine formal algebraic space is adic* when it is presented by successive
quotient spectra of an adic ring with a finitely generated ideal of definition. -/
@[mk_iff]
class IsAdicStarAffine {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) : Prop where
  /-- There is an adic ring, a finitely generated ideal of definition, and a
  structure morphism over `S` whose successive quotient spectra present `X`. -/
  exists_adicStar :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : TopologicalRing.IsAdicRing A) (I : Ideal A) (_ : I.FG)
      (_ : TopologicalRing.Ideal.IsIdealOfDefinition I)
      (_ : Spec (.of A) ⟶ S) (D : ℕ ⥤ Over S),
        (∀ n : ℕ,
            Nonempty ((D.obj n).left ≅ Spec (.of (A ⧸ I ^ (n + 1))))) ∧
          IsDirectedAffineThickeningColimit D X

namespace IsAdicStarAffine

/-- The representable functor of an affine scheme over `S` is an adic* affine
formal algebraic space. -/
instance instYoneda {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsAffine U.left] :
    IsAdicStarAffine (yoneda.obj U) :=
  sorry

/-- An adic* affine formal algebraic space is presented by an adic ring with a
finitely generated ideal of definition. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) [IsAdicStarAffine X] :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : TopologicalRing.IsAdicRing A) (I : Ideal A) (_ : I.FG)
      (_ : TopologicalRing.Ideal.IsIdealOfDefinition I)
      (_ : Spec (.of A) ⟶ S) (D : ℕ ⥤ Over S),
        (∀ n : ℕ,
            Nonempty ((D.obj n).left ≅ Spec (.of (A ⧸ I ^ (n + 1))))) ∧
          IsDirectedAffineThickeningColimit D X :=
  sorry

/-- Adic* affine formal algebraic spaces are exactly functors presented by an
adic ring with a finitely generated ideal of definition. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) :
    IsAdicStarAffine X ↔
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : TopologicalRing.IsAdicRing A) (I : Ideal A) (_ : I.FG)
        (_ : TopologicalRing.Ideal.IsIdealOfDefinition I)
        (_ : Spec (.of A) ⟶ S) (D : ℕ ⥤ Over S),
          (∀ n : ℕ,
              Nonempty ((D.obj n).left ≅ Spec (.of (A ⧸ I ^ (n + 1))))) ∧
            IsDirectedAffineThickeningColimit D X :=
  sorry

end IsAdicStarAffine

/-- A formal algebraic space over `S` is locally adic* when it admits an étale
atlas by adic* affine formal algebraic spaces. -/
@[mk_iff]
class IsLocallyAdicStar {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] : Prop where
  /-- There is an étale atlas by adic* affine formal algebraic spaces,
  representable by algebraic spaces and jointly fppf-locally surjective. -/
  exists_atlas :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, IsAdicStarAffine (cover i)) ∧
        (∀ i, AlgebraicSpace.representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : AlgebraicSpace.representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π)

namespace IsLocallyAdicStar

/-- A locally adic* formal algebraic space admits an étale atlas by adic*
affine formal algebraic spaces. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyAdicStar X] :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, IsAdicStarAffine (cover i)) ∧
        (∀ i, AlgebraicSpace.representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : AlgebraicSpace.representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) :=
  sorry

/-- Locally adic* formal algebraic spaces are exactly formal algebraic spaces
with an étale atlas by adic* affine charts. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] :
    IsLocallyAdicStar X ↔
      ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
        (∀ i, IsAdicStarAffine (cover i)) ∧
          (∀ i, AlgebraicSpace.representableByAlgebraicSpaces (π i)) ∧
            (∀ i (ha : AlgebraicSpace.representableByAlgebraicSpaces (π i))
              {U : Over S} (ξ : yoneda.obj U ⟶ X),
              AlgebraicSpace.Etale
                (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
              Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) :=
  sorry

end IsLocallyAdicStar

namespace IsAdicStarAffine

/-- An adic* affine formal algebraic space that is a formal algebraic space is
locally adic*. -/
instance instIsLocallyAdicStar {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsAdicStarAffine X] : IsLocallyAdicStar X :=
  sorry

end IsAdicStarAffine

/-- A formal algebraic space over `S` is locally countably indexed when it
admits an étale atlas by countably indexed affine formal algebraic spaces. -/
@[mk_iff]
class IsLocallyCountablyIndexed {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] : Prop where
  /-- There is an étale atlas by countably indexed affine formal algebraic
  spaces, representable by algebraic spaces and jointly fppf-locally
  surjective. -/
  exists_atlas :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, AffineFormalAlgebraicSpace.IsCountablyIndexedAffine (cover i)) ∧
        (∀ i, AlgebraicSpace.representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : AlgebraicSpace.representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π)

namespace IsLocallyCountablyIndexed

/-- A locally countably indexed formal algebraic space admits an étale atlas by
countably indexed affine formal algebraic spaces. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyCountablyIndexed X] :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, AffineFormalAlgebraicSpace.IsCountablyIndexedAffine (cover i)) ∧
        (∀ i, AlgebraicSpace.representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : AlgebraicSpace.representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) :=
  sorry

/-- Locally countably indexed formal algebraic spaces are exactly formal
algebraic spaces with an étale atlas by countably indexed affine charts. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] :
    IsLocallyCountablyIndexed X ↔
      ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
        (∀ i, AffineFormalAlgebraicSpace.IsCountablyIndexedAffine (cover i)) ∧
          (∀ i, AlgebraicSpace.representableByAlgebraicSpaces (π i)) ∧
            (∀ i (ha : AlgebraicSpace.representableByAlgebraicSpaces (π i))
              {U : Over S} (ξ : yoneda.obj U ⟶ X),
              AlgebraicSpace.Etale
                (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
              Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) :=
  sorry

end IsLocallyCountablyIndexed

end AlgebraicGeometry.FormalAlgebraicSpace

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace.IsCountablyIndexedAffine

/-- A countably indexed affine formal algebraic space that is a formal algebraic
space is locally countably indexed. -/
instance instIsLocallyCountablyIndexed {S : Scheme.{u}}
    (X : (Over S)ᵒᵖ ⥤ Type u)
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace X] [IsCountablyIndexedAffine X] :
    FormalAlgebraicSpace.IsLocallyCountablyIndexed X :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace.IsCountablyIndexedAffine
