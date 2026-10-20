module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.GeometricOrbit
public import Mathlib.Logic.Relation
public import stacks_project.Chap78.Definition_78_4_1_PreRelation
public import stacks_project.Chap66.Definition_66_19_1_GeometricPoint

/-!
# Geometric orbits of a pre-relation

This module records weak and ordinary equivalence of slice points of a pre-relation, together
with the corresponding orbit sets. Images of geometric `k`-points in an overfield are formed by
precomposition with the slice morphism of a field-valued factorization.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint.Factorization.sliceHom :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {p q : AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint X},
    AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint.Factorization p q →
      (Over.mk p.hom ⟶ Over.mk q.hom))

#check (AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint.Factorization.sliceHom_left :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {p q : AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint X}
    (φ : AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint.Factorization p q),
    (AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint.Factorization.sliceHom φ).left =
      AlgebraicGeometry.AlgebraicSpace.ofOverHomMk φ.schemeHom φ.fac_structure)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.weaklyEquivalent :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B},
    AlgebraicGeometry.AlgebraicSpace.PreRelation U →
      (T : Over B) → (x y : T ⟶ U) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.weaklyEquivalent_iff :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U) (T : Over B) (x y : T ⟶ U),
    AlgebraicGeometry.AlgebraicSpace.PreRelation.weaklyEquivalent P T x y ↔
      _root_.Relation.EqvGen (P.pointRel T) x y)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.weaklyEquivalent_equivalence :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U) (T : Over B),
    Equivalence (AlgebraicGeometry.AlgebraicSpace.PreRelation.weaklyEquivalent P T))

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.orbitEquivalent :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B},
    AlgebraicGeometry.AlgebraicSpace.PreRelation U →
      (b : AlgebraicGeometry.AlgebraicSpace.GeometricPoint B) →
      (x y : Over.mk b.hom ⟶ U) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.orbitEquivalent_iff :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U)
    (b : AlgebraicGeometry.AlgebraicSpace.GeometricPoint B)
    (x y : Over.mk b.hom ⟶ U),
    AlgebraicGeometry.AlgebraicSpace.PreRelation.orbitEquivalent P b x y ↔
      ∃ (q : AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint B)
        (φ : AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint.Factorization
          q b.toFieldValuedPoint),
        AlgebraicGeometry.AlgebraicSpace.PreRelation.weaklyEquivalent P (Over.mk q.hom)
          (φ.sliceHom ≫ x) (φ.sliceHom ≫ y))

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.weakOrbit :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B},
    AlgebraicGeometry.AlgebraicSpace.PreRelation U →
      (T : Over B) → (x : T ⟶ U) → Set (T ⟶ U))

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.mem_weakOrbit :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U) (T : Over B) (x y : T ⟶ U),
    y ∈ AlgebraicGeometry.AlgebraicSpace.PreRelation.weakOrbit P T x ↔
      AlgebraicGeometry.AlgebraicSpace.PreRelation.weaklyEquivalent P T x y)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.orbit :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B},
    AlgebraicGeometry.AlgebraicSpace.PreRelation U →
      (b : AlgebraicGeometry.AlgebraicSpace.GeometricPoint B) →
      (x : Over.mk b.hom ⟶ U) → Set (Over.mk b.hom ⟶ U))

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.mem_orbit :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U)
    (b : AlgebraicGeometry.AlgebraicSpace.GeometricPoint B)
    (x y : Over.mk b.hom ⟶ U),
    y ∈ AlgebraicGeometry.AlgebraicSpace.PreRelation.orbit P b x ↔
      AlgebraicGeometry.AlgebraicSpace.PreRelation.orbitEquivalent P b x y)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.weaklyEquivalent_imp_orbitEquivalent :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U)
    (b : AlgebraicGeometry.AlgebraicSpace.GeometricPoint B)
    (x y : Over.mk b.hom ⟶ U),
    AlgebraicGeometry.AlgebraicSpace.PreRelation.weaklyEquivalent P (Over.mk b.hom) x y →
      AlgebraicGeometry.AlgebraicSpace.PreRelation.orbitEquivalent P b x y)
