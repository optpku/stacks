/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_9_4_Induction
public import stacks_project.Chap75.Remark_75_9_5_AffineDiagonal

/-!
# Collections for qcqs induction on the spaces-étale site

Lemma 75.9.4 applies to any collection `B` of objects of `X_spaces,étale`
satisfying the quasi-compactness, quasi-separatedness, quasi-compact open, and
affine-membership conditions. This module names those conditions and the three
standard examples from Remark 75.9.5.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A collection `B` of objects of `X_spaces,étale` satisfies the standing
hypotheses (1), (2), and (3)(a) of `qcqsSpacesEtale_induction_mem`. -/
structure QcqsSpacesEtaleInductionSet {S : Scheme.{u}} {X : AlgebraicSpace S}
    (B : Set (spacesEtaleSite X)) : Prop where
  /-- Every member of `B` is quasi-compact. -/
  isQuasiCompact : ∀ W ∈ B, IsQuasiCompact W.left
  /-- Every member of `B` is absolutely quasi-separated. -/
  isAbsolutelyQuasiSeparated : ∀ W ∈ B, IsAbsolutelyQuasiSeparated W.left
  /-- `B` is closed under quasi-compact open immersions in the site. -/
  mem_open : ∀ {U W : spacesEtaleSite X} (j : U ⟶ W)
    [IsOpenImmersion j.left] [IsQuasiCompact U.left], W ∈ B → U ∈ B
  /-- Every affine object of the site lies in `B`. -/
  mem_affine : ∀ (V : spacesEtaleSite X) [IsAffine V.left], V ∈ B

/-- Package the four standing conditions of Lemma 75.9.4 (1), (2), and (3)(a). -/
def QcqsSpacesEtaleInductionSet.of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (B : Set (spacesEtaleSite X))
    (isQuasiCompact : ∀ W ∈ B, IsQuasiCompact W.left)
    (isAbsolutelyQuasiSeparated : ∀ W ∈ B, IsAbsolutelyQuasiSeparated W.left)
    (mem_open : ∀ {U W : spacesEtaleSite X} (j : U ⟶ W)
      [IsOpenImmersion j.left] [IsQuasiCompact U.left], W ∈ B → U ∈ B)
    (mem_affine : ∀ (V : spacesEtaleSite X) [IsAffine V.left], V ∈ B) :
    QcqsSpacesEtaleInductionSet B where
  isQuasiCompact := isQuasiCompact
  isAbsolutelyQuasiSeparated := isAbsolutelyQuasiSeparated
  mem_open := mem_open
  mem_affine := mem_affine

/-- The packaged conditions are exactly quasi-compactness and absolute
quasi-separatedness of members, closure under quasi-compact opens, and
membership of every affine object. -/
theorem QcqsSpacesEtaleInductionSet.spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    {B : Set (spacesEtaleSite X)} (hB : QcqsSpacesEtaleInductionSet B) :
    (∀ W ∈ B, IsQuasiCompact W.left) ∧
      (∀ W ∈ B, IsAbsolutelyQuasiSeparated W.left) ∧
      (∀ {U W : spacesEtaleSite X} (j : U ⟶ W)
        [IsOpenImmersion j.left] [IsQuasiCompact U.left], W ∈ B → U ∈ B) ∧
      (∀ (V : spacesEtaleSite X) [IsAffine V.left], V ∈ B) :=
  sorry

/-- Quasi-compact absolutely separated objects of `X_spaces,étale`. -/
def qcAbsolutelySeparatedSpacesEtale {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Set (spacesEtaleSite X) :=
  {W | IsQuasiCompact W.left ∧ IsAbsolutelySeparated W.left}

/-- Membership in `qcAbsolutelySeparatedSpacesEtale X` is quasi-compactness
together with absolute separatedness of the underlying algebraic space. -/
theorem mem_qcAbsolutelySeparatedSpacesEtale {S : Scheme.{u}}
    {X : AlgebraicSpace S} {W : spacesEtaleSite X} :
    W ∈ qcAbsolutelySeparatedSpacesEtale X ↔
      IsQuasiCompact W.left ∧ IsAbsolutelySeparated W.left :=
  sorry

/-- Quasi-compact objects of `X_spaces,étale` with affine diagonal over the
terminal scheme. -/
def qcAbsolutelyAffineDiagonalSpacesEtale {S : Scheme.{u}}
    (X : AlgebraicSpace S) : Set (spacesEtaleSite X) :=
  {W | IsQuasiCompact W.left ∧ IsAbsolutelyAffineDiagonal W.left}

/-- Membership in `qcAbsolutelyAffineDiagonalSpacesEtale X` is quasi-compactness
together with absolute affine-diagonality of the underlying algebraic space. -/
theorem mem_qcAbsolutelyAffineDiagonalSpacesEtale {S : Scheme.{u}}
    {X : AlgebraicSpace S} {W : spacesEtaleSite X} :
    W ∈ qcAbsolutelyAffineDiagonalSpacesEtale X ↔
      IsQuasiCompact W.left ∧ IsAbsolutelyAffineDiagonal W.left :=
  sorry

/-- Quasi-compact objects of `X_spaces,étale` that are open subspaces of `X` or
open subspaces of an affine object of the site. -/
def qcqsGeneratedSpacesEtale {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Set (spacesEtaleSite X) :=
  {W | IsQuasiCompact W.left ∧
    (IsOpenImmersion W.hom ∨
      ∃ (V : spacesEtaleSite X) (j : W ⟶ V),
        IsAffine V.left ∧ IsOpenImmersion j.left)}

/-- Membership in `qcqsGeneratedSpacesEtale X` is quasi-compactness together with
being an open subspace of `X` or an open of an affine object of the site. -/
theorem mem_qcqsGeneratedSpacesEtale_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {W : spacesEtaleSite X} :
    W ∈ qcqsGeneratedSpacesEtale X ↔
      IsQuasiCompact W.left ∧
        (IsOpenImmersion W.hom ∨
          ∃ (V : spacesEtaleSite X) (j : W ⟶ V),
            IsAffine V.left ∧ IsOpenImmersion j.left) :=
  sorry

/-- The final object `spacesEtaleSite.self X` is a quasi-compact open subspace of
`X`, hence lies in `qcqsGeneratedSpacesEtale X`. -/
theorem self_mem_qcqsGeneratedSpacesEtale {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] :
    spacesEtaleSite.self X ∈ qcqsGeneratedSpacesEtale X :=
  sorry

/-- For quasi-compact quasi-separated `X`, the generated collection satisfies
(1), (2), and (3)(a) of Lemma 75.9.4. -/
theorem qcqsGeneratedSpacesEtale_isInductionSet {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] :
    QcqsSpacesEtaleInductionSet (qcqsGeneratedSpacesEtale X) :=
  sorry

/-- The generated collection is contained in every collection that contains `X`
and satisfies (1), (2), and (3)(a) of Lemma 75.9.4. -/
theorem qcqsGeneratedSpacesEtale_subset {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    {B : Set (spacesEtaleSite X)} (h_self : spacesEtaleSite.self X ∈ B)
    (hB : QcqsSpacesEtaleInductionSet B) :
    qcqsGeneratedSpacesEtale X ⊆ B :=
  sorry

/-- Applying `qcqsSpacesEtale_induction_mem` to
`qcAbsolutelySeparatedSpacesEtale X` recovers the induction principle of
Lemma 75.9.3 for quasi-compact absolutely separated objects of the site. -/
theorem qcqsSpacesEtale_induction_of_absolutelySeparated {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelySeparated X]
    (P : spacesEtaleSite X → Prop)
    (h_affine : ∀ (W : spacesEtaleSite X) [IsAffine W.left], P W)
    (h_square : ∀ {U V W : spacesEtaleSite X} (j : U ⟶ W) (f : V ⟶ W)
      [IsElementaryDistinguishedSquare j.left f.left] [Etale f.left]
      [IsQuasiCompact W.left] [IsAbsolutelySeparated W.left]
      [IsQuasiCompact U.left] [IsAffine V.left],
      P U → P V → P (spacesEtaleSite.fiber j f) → P W)
    (W : spacesEtaleSite X) [IsQuasiCompact W.left] [IsAbsolutelySeparated W.left] :
    P W :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
