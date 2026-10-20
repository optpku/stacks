module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Induction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.AbsoluteAffineDiagonal

/-!
# Collections for qcqs induction on the spaces-étale site

Collections of objects of `X_spaces,étale` support quasi-compact quasi-separated
induction when their members are quasi-compact and absolutely quasi-separated,
they are closed under quasi-compact opens, and they contain every affine object.
Examples arise from absolute separatedness, absolute affine-diagonality, and
quasi-compact opens of the base space or affine objects of the site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A collection of quasi-compact absolutely quasi-separated spaces-étale objects
that is closed under quasi-compact opens and contains every affine object. -/
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

/-- Construct an induction collection from quasi-compactness and absolute
quasi-separatedness of its members, closure under quasi-compact opens, and
membership of every affine object. -/
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

/-- For quasi-compact absolutely quasi-separated `X`, the generated collection
is an induction collection. -/
theorem qcqsGeneratedSpacesEtale_isInductionSet {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] :
    QcqsSpacesEtaleInductionSet (qcqsGeneratedSpacesEtale X) :=
  sorry

/-- The generated collection is contained in every induction collection that
contains the identity object of the spaces-étale site. -/
theorem qcqsGeneratedSpacesEtale_subset {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    {B : Set (spacesEtaleSite X)} (h_self : spacesEtaleSite.self X ∈ B)
    (hB : QcqsSpacesEtaleInductionSet B) :
    qcqsGeneratedSpacesEtale X ⊆ B :=
  sorry

/-- For quasi-compact absolutely separated `X`, the quasi-compact absolutely
separated site objects form an induction collection containing the identity object. -/
theorem qcAbsolutelySeparatedSpacesEtale_spec {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelySeparated X] :
    spacesEtaleSite.self X ∈ qcAbsolutelySeparatedSpacesEtale X ∧
      QcqsSpacesEtaleInductionSet (qcAbsolutelySeparatedSpacesEtale X) :=
  sorry

/-- For quasi-compact `X` with absolute affine diagonal, the quasi-compact site
objects with absolute affine diagonal form an induction collection containing
the identity object. -/
theorem qcAbsolutelyAffineDiagonalSpacesEtale_spec {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelyAffineDiagonal X] :
    spacesEtaleSite.self X ∈ qcAbsolutelyAffineDiagonalSpacesEtale X ∧
      QcqsSpacesEtaleInductionSet (qcAbsolutelyAffineDiagonalSpacesEtale X) :=
  sorry

/-- For quasi-compact absolutely quasi-separated `X`, the quasi-compact opens of
`X` and of affine site objects form the smallest induction collection containing
the identity object. -/
theorem qcqsGeneratedSpacesEtale_spec {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] :
    qcqsGeneratedSpacesEtale X =
      sInf {B | spacesEtaleSite.self X ∈ B ∧ QcqsSpacesEtaleInductionSet B} :=
  sorry

/-- A property holding on affine objects and preserved by elementary distinguished
squares with quasi-compact absolutely separated target, quasi-compact open part,
and affine étale part holds on all quasi-compact absolutely separated site objects. -/
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
