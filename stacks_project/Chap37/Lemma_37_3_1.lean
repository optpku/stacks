/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Morphisms.Thickening
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.3.1 (1): affine morphisms are invariant under a morphism of thickenings. -/
@[stacks 09ZV] #check (AlgebraicGeometry.Thickening.Hom.isAffineHom_iff :
  ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U),
    AlgebraicGeometry.IsAffineHom g.left ↔ AlgebraicGeometry.IsAffineHom g.right)

/- Lemma 37.3.1 (2): surjective morphisms are invariant under a morphism of thickenings. -/
@[stacks 09ZV] #check (AlgebraicGeometry.Thickening.Hom.surjective_iff :
  ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U),
    AlgebraicGeometry.Surjective g.left ↔ AlgebraicGeometry.Surjective g.right)

/- Lemma 37.3.1 (3): quasi-compact morphisms are invariant under a morphism of thickenings. -/
@[stacks 09ZV] #check (AlgebraicGeometry.Thickening.Hom.quasiCompact_iff :
  ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U),
    AlgebraicGeometry.QuasiCompact g.left ↔ AlgebraicGeometry.QuasiCompact g.right)

/- Lemma 37.3.1 (4): universally closed morphisms are invariant under a morphism of
thickenings. -/
@[stacks 09ZV] #check (AlgebraicGeometry.Thickening.Hom.universallyClosed_iff :
  ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U),
    AlgebraicGeometry.UniversallyClosed g.left ↔
      AlgebraicGeometry.UniversallyClosed g.right)

/- Lemma 37.3.1 (5): integral morphisms are invariant under a morphism of thickenings. -/
@[stacks 09ZV] #check (AlgebraicGeometry.Thickening.Hom.isIntegralHom_iff :
  ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U),
    AlgebraicGeometry.IsIntegralHom g.left ↔ AlgebraicGeometry.IsIntegralHom g.right)

/- Lemma 37.3.1 (6): separated morphisms are invariant under a morphism of thickenings. -/
@[stacks 09ZV] #check (AlgebraicGeometry.Thickening.Hom.isSeparated_iff :
  ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U),
    AlgebraicGeometry.IsSeparated g.left ↔ AlgebraicGeometry.IsSeparated g.right)

/- Lemma 37.3.1 (7): quasi-separated morphisms are invariant under a morphism of
thickenings. -/
@[stacks 09ZV] #check (AlgebraicGeometry.Thickening.Hom.quasiSeparated_iff :
  ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U),
    AlgebraicGeometry.QuasiSeparated g.left ↔ AlgebraicGeometry.QuasiSeparated g.right)

/- Lemma 37.3.1 (8): universally injective morphisms are invariant under a morphism of
thickenings. -/
@[stacks 09ZV] #check (AlgebraicGeometry.Thickening.Hom.universallyInjective_iff :
  ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U),
    AlgebraicGeometry.UniversallyInjective g.left ↔
      AlgebraicGeometry.UniversallyInjective g.right)

/- Lemma 37.3.1 (9): universally open morphisms are invariant under a morphism of
thickenings. -/
@[stacks 09ZV] #check (AlgebraicGeometry.Thickening.Hom.universallyOpen_iff :
  ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U),
    AlgebraicGeometry.UniversallyOpen g.left ↔ AlgebraicGeometry.UniversallyOpen g.right)

/- Lemma 37.3.1 (10): quasi-affine morphisms are invariant under a morphism of thickenings. -/
@[stacks 09ZV] #check (AlgebraicGeometry.Thickening.Hom.quasiAffineHom_iff :
  ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U),
    AlgebraicGeometry.QuasiAffineHom g.left ↔ AlgebraicGeometry.QuasiAffineHom g.right)
