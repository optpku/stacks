/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.SetTheoreticInvariant
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

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsSetTheoreticallyInvariant :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B},
    PreRelation U → (U ⟶ X) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.isSetTheoreticallyInvariant_iff :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (f : U ⟶ X),
    PreRelation.IsSetTheoreticallyInvariant P f ↔
      ∀ (kbar : GeometricPoint B) (r : Over.mk kbar.hom ⟶ P.left),
        r ≫ P.s ≫ f = r ≫ P.t ≫ f)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.isSetTheoreticallyInvariant_pointRel :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    {P : PreRelation U} {f : U ⟶ X},
    PreRelation.IsSetTheoreticallyInvariant P f →
      ∀ {kbar : GeometricPoint B} {x y : Over.mk kbar.hom ⟶ U},
        P.pointRel (Over.mk kbar.hom) x y → x ≫ f = y ≫ f)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.SeparatesOrbits :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B},
    PreRelation U → (U ⟶ X) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.SeparatesOrbits.of :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    {P : PreRelation U} {f : U ⟶ X},
    PreRelation.IsSetTheoreticallyInvariant P f →
      (∀ (kbar : GeometricPoint B) (x y : Over.mk kbar.hom ⟶ U),
        x ≫ f = y ≫ f → PreRelation.orbitEquivalent P kbar x y) →
      PreRelation.SeparatesOrbits P f)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.separatesOrbits_iff :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (f : U ⟶ X),
    PreRelation.SeparatesOrbits P f ↔
      PreRelation.IsSetTheoreticallyInvariant P f ∧
        ∀ (kbar : GeometricPoint B) (x y : Over.mk kbar.hom ⟶ U),
          x ≫ f = y ≫ f → PreRelation.orbitEquivalent P kbar x y)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.separatesOrbits_spec :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    {P : PreRelation U} {f : U ⟶ X},
    PreRelation.SeparatesOrbits P f →
      PreRelation.IsSetTheoreticallyInvariant P f ∧
        ∀ (kbar : GeometricPoint B) (x y : Over.mk kbar.hom ⟶ U),
          x ≫ f = y ≫ f → y ∈ PreRelation.orbit P kbar x)
