module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.DimensionZero
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver

/-!
# Finite local-Artinian coproduct presentations of algebraic spaces

An algebraic space over a field may be presented, up to isomorphism over the
base, as the algebraic space associated to a coproduct of spectra of
finite-dimensional local Artinian algebras over that field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {k : Type u} [Field k]

/-- Explicit data presenting an algebraic space over a field as isomorphic over
that field to a coproduct of spectra of finite-dimensional local Artinian
algebras. -/
structure FiniteLocalArtinianCoproduct (X : AlgebraicSpace (Spec (CommRingCat.of k))) where
  /-- The scheme over the base field carrying the coproduct presentation. -/
  scheme : SchemeOverField k
  /-- An isomorphism of algebraic spaces over `Spec k` with the algebraic space
  associated to `scheme`. -/
  iso : X ≅ ofOver scheme
  /-- The scheme-level finite local-Artinian coproduct presentation of `scheme`. -/
  coproduct : SchemeOverField.FiniteLocalArtinianCoproduct scheme

namespace FiniteLocalArtinianCoproduct

/-- Package a scheme-level finite local-Artinian coproduct presentation together
with an isomorphism of algebraic spaces over `Spec k`. -/
def ofScheme {X : AlgebraicSpace (Spec (CommRingCat.of k))} {T : SchemeOverField k}
    (D : SchemeOverField.FiniteLocalArtinianCoproduct T) (e : X ≅ ofOver T) :
    FiniteLocalArtinianCoproduct X where
  scheme := T
  iso := e
  coproduct := D

/-- Package a disjoint union of spectra of finite-dimensional local Artinian
`k`-algebras, together with an isomorphism of algebraic spaces over `Spec k`, as
a finite local-Artinian coproduct presentation. -/
def ofSigmaSpec {X : AlgebraicSpace (Spec (CommRingCat.of k))} (ι : Type u)
    (A : ι → CommAlgOverField k) (isLocalRing : ∀ i, IsLocalRing (A i))
    (isArtinianRing : ∀ i, IsArtinianRing (A i))
    (finiteDimensional : ∀ i, FiniteDimensional k (A i))
    (e : X ≅ ofOver (SchemeOverField.sigmaSpec ι A)) :
    FiniteLocalArtinianCoproduct X :=
  ofScheme
    { ι
      algebra := A
      isLocalRing
      isArtinianRing
      finiteDimensional
      iso := Iso.refl (SchemeOverField.sigmaSpec ι A) }
    e

/-- A finite local-Artinian coproduct presentation of an algebraic space exposes
the local, Artinian, and finite-dimensional conditions on its component algebras,
together with an isomorphism over `Spec k` to the associated coproduct of
spectra. -/
theorem spec {X : AlgebraicSpace (Spec (CommRingCat.of k))}
    (D : FiniteLocalArtinianCoproduct X) :
    (∀ i : D.coproduct.ι, IsLocalRing (D.coproduct.algebra i)) ∧
      (∀ i : D.coproduct.ι, IsArtinianRing (D.coproduct.algebra i)) ∧
      (∀ i : D.coproduct.ι, FiniteDimensional k (D.coproduct.algebra i)) ∧
      Nonempty
        (X ≅ ofOver (SchemeOverField.sigmaSpec D.coproduct.ι D.coproduct.algebra)) :=
  sorry

end FiniteLocalArtinianCoproduct

end AlgebraicGeometry.AlgebraicSpace
