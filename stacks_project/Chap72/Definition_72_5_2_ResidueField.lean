module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap68.Definition_68_22_1_GenericPoints
public import stacks_project.Chap68.Lemma_68_11_3
public import stacks_project.Chap72.Definition_72_4_1_Integral

/-!
# Residue-field homomorphisms and degrees of morphisms of algebraic spaces

A morphism of decent algebraic spaces induces a residue-field homomorphism
`κ(f(x)) ⟶ κ(x)` from the unique residue-point factorization. The residue
degree at `x` is the finrank of this extension, and an irreducible decent
algebraic space has a unique generic point at which the source-facing degree is
evaluated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An irreducible decent algebraic space has a generic point. -/
theorem exists_mem_genericPoints {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] [IsIrreducible X] : ∃ x, x ∈ genericPoints X :=
  sorry

/-- An irreducible decent algebraic space has at most one generic point. -/
theorem eq_of_mem_genericPoints {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] [IsIrreducible X] {x y : Points X}
    (hx : x ∈ genericPoints X) (hy : y ∈ genericPoints X) : x = y :=
  sorry

namespace Hom

open FieldValuedPoint

/-- The unique factorization of `Spec(κ(x)) ⟶ Y` through
`Spec(κ(Points.map f x)) ⟶ Y`. -/
noncomputable def residuePointFactor {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (x : Points X) :
    Factorization ((residuePoint x).map f) (residuePoint (Points.map f x)) :=
  Classical.choice (exists_residuePointFactor f x)

/-- The residue-point factorization is the unique factorization of
`(residuePoint x).map f` through `residuePoint (Points.map f x)`. -/
theorem residuePointFactor_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (x : Points X)
    (φ : Factorization ((residuePoint x).map f)
      (residuePoint (Points.map f x))) :
    residuePointFactor f x = φ :=
  sorry

/-- The residue-field homomorphism `κ(f(x)) ⟶ κ(x)` induced by a morphism of
decent algebraic spaces. -/
noncomputable def residueFieldHom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (x : Points X) :
    Y.residueField (Points.map f x) ⟶ X.residueField x :=
  Spec.homEquiv (residuePointFactor f x).schemeHom

/-- The identity morphism induces the identity on residue fields. -/
theorem residueFieldHom_id {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (x : Points X) :
    residueFieldHom (𝟙 X) x =
      eqToHom (congrArg X.residueField (Points.map_id x)) :=
  sorry

/-- Residue-field homomorphisms compose contravariantly. -/
theorem residueFieldHom_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] [IsDecent Z] (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Points X) :
    residueFieldHom (f ≫ g) x =
      eqToHom (congrArg Z.residueField (Points.map_comp f g x)) ≫
        residueFieldHom g (Points.map f x) ≫ residueFieldHom f x :=
  sorry

/-- `Spec.map` recovers the source-spectrum map of the residue-point
factorization. -/
theorem specMap_residueFieldHom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (x : Points X) :
    Spec.map (residueFieldHom f x) = (residuePointFactor f x).schemeHom :=
  sorry

/-- The residue degree of `f` at `x` is the finrank of `κ(x)` over `κ(f(x))`,
or `0` if the extension is infinite. -/
noncomputable def residueDegree {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (x : Points X) : ℕ :=
  -- Local instance justification (instance diamond): competing morphisms induce competing algebras on the same residue fields
  letI := (residueFieldHom f x).hom.toAlgebra
  Module.finrank (Y.residueField (Points.map f x)) (X.residueField x)

/-- The residue degree is the finrank of the algebra induced by
`residueFieldHom`. -/
theorem residueDegree_eq_finrank {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (x : Points X) :
    residueDegree f x =
      -- Local instance justification (instance diamond): competing morphisms induce competing algebras on the same residue fields
      letI := (residueFieldHom f x).hom.toAlgebra
      Module.finrank (Y.residueField (Points.map f x)) (X.residueField x) :=
  sorry

/-- The identity morphism has residue degree `1` at every point. -/
theorem residueDegree_id {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (x : Points X) : residueDegree (𝟙 X) x = 1 :=
  sorry

/-- The residue-field extension of `f` at `x` is finite. -/
def FiniteResidueFieldExtensionAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (x : Points X) : Prop :=
  -- Local instance justification (instance diamond): competing morphisms induce competing algebras on the same residue fields
  letI := (residueFieldHom f x).hom.toAlgebra
  FiniteDimensional (Y.residueField (Points.map f x)) (X.residueField x)

/-- Finiteness of the residue-field extension at `x` is finite-dimensionality
of the algebra induced by `residueFieldHom`. -/
theorem FiniteResidueFieldExtensionAt_iff {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsDecent X] [IsDecent Y] (f : X ⟶ Y)
    (x : Points X) :
    FiniteResidueFieldExtensionAt f x ↔
      -- Local instance justification (instance diamond): competing morphisms induce competing algebras on the same residue fields
      letI := (residueFieldHom f x).hom.toAlgebra
      FiniteDimensional (Y.residueField (Points.map f x))
        (X.residueField x) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
