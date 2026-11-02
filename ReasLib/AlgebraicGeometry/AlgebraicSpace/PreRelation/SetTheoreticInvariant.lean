/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.GeometricOrbit
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Invariant

/-!
# Set-theoretic invariance and orbit-separation

This module records when a morphism of algebraic spaces over a base equalizes a pre-relation
on geometric points, and when it moreover separates geometric `R`-orbits.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- A morphism `f : U ⟶ X` over `B` is set-theoretically invariant for a pre-relation `P` when
the induced map on geometric `k`-points equalizes `P.s` and `P.t` for every algebraically closed
field `k` over `B`. -/
def IsSetTheoreticallyInvariant {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (f : U ⟶ X) : Prop :=
  ∀ (kbar : GeometricPoint B) (r : Over.mk kbar.hom ⟶ P.left),
    r ≫ P.s ≫ f = r ≫ P.t ≫ f

/-- A morphism invariant under a pre-relation is set-theoretically invariant. -/
theorem isSetTheoreticallyInvariant_of_isInvariant {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) {φ : U ⟶ X} (h : P.IsInvariantHom φ) :
    P.IsSetTheoreticallyInvariant φ := by
  intro kbar r
  exact congrArg (fun g => r ≫ g) h.symm

/-- Set-theoretic invariance is equalization of the two projections on geometric points. -/
theorem isSetTheoreticallyInvariant_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) (f : U ⟶ X) :
    IsSetTheoreticallyInvariant P f ↔
      ∀ (kbar : GeometricPoint B) (r : Over.mk kbar.hom ⟶ P.left),
        r ≫ P.s ≫ f = r ≫ P.t ≫ f := Iff.rfl

/-- On geometric points, relatedness for `P` implies equal images under a set-theoretically
invariant morphism. -/
theorem isSetTheoreticallyInvariant_pointRel {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} {P : PreRelation U} {f : U ⟶ X} (hf : IsSetTheoreticallyInvariant P f)
    {kbar : GeometricPoint B} {x y : Over.mk kbar.hom ⟶ U}
    (hxy : P.pointRel (Over.mk kbar.hom) x y) : x ≫ f = y ≫ f := by
  obtain ⟨r, rfl, rfl⟩ := hxy
  simpa only [Category.assoc] using (hf kbar r).symm

/-- A morphism `f : U ⟶ X` over `B` separates orbits of a pre-relation `P` when it is
set-theoretically invariant and equal images in `X(k)` imply the same geometric `R`-orbit on
`U(k)`. -/
structure SeparatesOrbits {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (f : U ⟶ X) : Prop where
  /-- The morphism is set-theoretically invariant for the pre-relation. -/
  isSetTheoreticallyInvariant : IsSetTheoreticallyInvariant P f
  /-- Equal images in `X(k)` imply the same geometric `R`-orbit on `U(k)`. -/
  eq_orbitEquivalent : ∀ (kbar : GeometricPoint B) (x y : Over.mk kbar.hom ⟶ U),
    x ≫ f = y ≫ f → orbitEquivalent P kbar x y

/-- Build a `SeparatesOrbits` witness from set-theoretic invariance and separation of geometric
`R`-orbits. -/
def SeparatesOrbits.of {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    {P : PreRelation U} {f : U ⟶ X} (h_inv : IsSetTheoreticallyInvariant P f)
    (h_sep : ∀ (kbar : GeometricPoint B) (x y : Over.mk kbar.hom ⟶ U),
      x ≫ f = y ≫ f → orbitEquivalent P kbar x y) : SeparatesOrbits P f where
  isSetTheoreticallyInvariant := h_inv
  eq_orbitEquivalent := h_sep

/-- Separating orbits is set-theoretic invariance together with recovery of geometric `R`-orbits
from equal images. -/
theorem separatesOrbits_iff {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (f : U ⟶ X) :
    SeparatesOrbits P f ↔
      IsSetTheoreticallyInvariant P f ∧
        ∀ (kbar : GeometricPoint B) (x y : Over.mk kbar.hom ⟶ U),
          x ≫ f = y ≫ f → orbitEquivalent P kbar x y :=
  ⟨fun h => ⟨h.isSetTheoreticallyInvariant, h.eq_orbitEquivalent⟩,
    fun h => SeparatesOrbits.of h.1 h.2⟩

/-- A morphism that separates orbits is set-theoretically invariant and identifies equal images
with membership in the same geometric `R`-orbit. -/
theorem separatesOrbits_spec {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    {P : PreRelation U} {f : U ⟶ X} (h : SeparatesOrbits P f) :
    IsSetTheoreticallyInvariant P f ∧
      ∀ (kbar : GeometricPoint B) (x y : Over.mk kbar.hom ⟶ U),
        x ≫ f = y ≫ f → y ∈ orbit P kbar x :=
  ⟨h.isSetTheoreticallyInvariant, h.eq_orbitEquivalent⟩

/-- A morphism over the base is set-theoretically invariant for a pre-relation if and only if
its induced map on geometric points is constant on geometric orbits over every algebraically
closed field over the base. -/
@[stacks 048W]
theorem isSetTheoreticallyInvariant_iff_constantOnOrbits
    {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) :
    P.IsSetTheoreticallyInvariant φ ↔
      ∀ (kbar : GeometricPoint B) (x y : Over.mk kbar.hom ⟶ U),
        y ∈ P.orbit kbar x → x ≫ φ = y ≫ φ := by
  constructor
  · intro hφ kbar x y hxy
    sorry
  · intro hφ kbar r
    have hid : (FieldValuedPoint.Factorization.refl kbar.toFieldValuedPoint).sliceHom =
        𝟙 (Over.mk kbar.hom) := by
      apply Over.OverMorphism.ext
      change yoneda.map (𝟙 kbar.overObj) = 𝟙 _
      exact yoneda.map_id _
    have horbit : (r ≫ P.s) ∈ P.orbit kbar (r ≫ P.t) := by
      refine ⟨kbar.toFieldValuedPoint, FieldValuedPoint.Factorization.refl _, ?_⟩
      change P.weaklyEquivalent (Over.mk kbar.hom)
        ((FieldValuedPoint.Factorization.refl kbar.toFieldValuedPoint).sliceHom ≫ (r ≫ P.t))
        ((FieldValuedPoint.Factorization.refl kbar.toFieldValuedPoint).sliceHom ≫ (r ≫ P.s))
      refine _root_.Relation.EqvGen.rel _ _ ⟨r, ?_, ?_⟩
      · rw [hid]
        exact (Category.id_comp (r ≫ P.t)).symm
      · rw [hid]
        exact (Category.id_comp (r ≫ P.s)).symm
    simpa only [Category.assoc] using (hφ kbar (r ≫ P.t) (r ≫ P.s) horbit).symm

/-- A set-theoretically invariant morphism is constant on geometric `R`-orbits. -/
theorem eq_comp_of_mem_orbit {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    {P : PreRelation U} {φ : U ⟶ X} (hφ : P.IsSetTheoreticallyInvariant φ)
    {kbar : GeometricPoint B} {x y : Over.mk kbar.hom ⟶ U} (h : y ∈ P.orbit kbar x) :
    x ≫ φ = y ≫ φ :=
  (isSetTheoreticallyInvariant_iff_constantOnOrbits P φ).mp hφ kbar x y h

end AlgebraicGeometry.AlgebraicSpace.PreRelation
