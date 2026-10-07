module

public import stacks_project.Chap83.Definition_83_5_4_Orbit

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

/-- Set-theoretic invariance is equalization of the two projections on geometric points. -/
theorem isSetTheoreticallyInvariant_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) (f : U ⟶ X) :
    IsSetTheoreticallyInvariant P f ↔
      ∀ (kbar : GeometricPoint B) (r : Over.mk kbar.hom ⟶ P.left),
        r ≫ P.s ≫ f = r ≫ P.t ≫ f := sorry

/-- On geometric points, relatedness for `P` implies equal images under a set-theoretically
invariant morphism. -/
theorem isSetTheoreticallyInvariant_pointRel {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} {P : PreRelation U} {f : U ⟶ X} (hf : IsSetTheoreticallyInvariant P f)
    {kbar : GeometricPoint B} {x y : Over.mk kbar.hom ⟶ U}
    (hxy : P.pointRel (Over.mk kbar.hom) x y) : x ≫ f = y ≫ f := sorry

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
          x ≫ f = y ≫ f → orbitEquivalent P kbar x y := sorry

/-- A morphism that separates orbits is set-theoretically invariant and identifies equal images
with membership in the same geometric `R`-orbit. -/
theorem separatesOrbits_spec {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    {P : PreRelation U} {f : U ⟶ X} (h : SeparatesOrbits P f) :
    IsSetTheoreticallyInvariant P f ∧
      ∀ (kbar : GeometricPoint B) (x y : Over.mk kbar.hom ⟶ U),
        x ≫ f = y ≫ f → y ∈ orbit P kbar x := sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
