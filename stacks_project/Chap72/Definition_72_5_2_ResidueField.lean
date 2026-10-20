/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap68.Definition_68_22_1_GenericPoints
public import stacks_project.Chap68.Lemma_68_11_3
public import stacks_project.Chap72.Definition_72_4_1_Integral

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidueField.Degree

/-!
# Compatibility for residue-field maps and degrees

The residue-field homomorphism name remains available for source consumers,
while the generic-point facts and residue-degree API use shared owners.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.exists_mem_genericPoints :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] [IsIrreducible X],
    ∃ x, x ∈ genericPoints X)

#check (AlgebraicGeometry.AlgebraicSpace.eq_of_mem_genericPoints :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] [IsIrreducible X] {x y : Points X}
    (hx : x ∈ genericPoints X) (hy : y ∈ genericPoints X),
    x = y)

namespace Hom

open FieldValuedPoint

/-- The residue-field map induced by a morphism of decent algebraic spaces. -/
noncomputable abbrev residueFieldHom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (x : Points X) :
    Y.residueField (Points.map f x) ⟶ X.residueField x :=
  residueFieldMap f x

#check (AlgebraicGeometry.AlgebraicSpace.Hom.residueFieldMap_id :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (x : Points X),
    residueFieldMap (𝟙 X) x =
      eqToHom (congrArg X.residueField (Points.map_id x)))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.residueFieldMap_comp :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] [IsDecent Z] (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Points X),
    residueFieldMap (f ≫ g) x =
      eqToHom (congrArg Z.residueField (Points.map_comp f g x)) ≫
        residueFieldMap g (Points.map f x) ≫ residueFieldMap f x)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.specMap_residueFieldMap :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (x : Points X)
    (φ : Factorization ((residuePoint x).map f)
      (residuePoint (Points.map f x))),
    Spec.map (residueFieldMap f x) = φ.schemeHom)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.residueDegree :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (x : Points X),
    ℕ)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.residueDegree_eq_finrank :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (x : Points X),
    residueDegree f x =
      -- Local instance justification (instance diamond): competing morphisms induce competing algebras on the same residue fields
      letI := (residueFieldMap f x).hom.toAlgebra
      Module.finrank (Y.residueField (Points.map f x)) (X.residueField x))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.residueDegree_id :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (x : Points X),
    residueDegree (𝟙 X) x = 1)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.FiniteResidueFieldExtensionAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (x : Points X),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.FiniteResidueFieldExtensionAt_iff :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsDecent X] [IsDecent Y] (f : X ⟶ Y)
    (x : Points X),
    FiniteResidueFieldExtensionAt f x ↔
      -- Local instance justification (instance diamond): competing morphisms induce competing algebras on the same residue fields
      letI := (residueFieldMap f x).hom.toAlgebra
      FiniteDimensional (Y.residueField (Points.map f x))
        (X.residueField x))

end Hom

end AlgebraicGeometry.AlgebraicSpace
