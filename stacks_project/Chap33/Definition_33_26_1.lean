/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Variety.AffinePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Variety.ProjectivePresentation

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Definition 33.26.1

An affine, projective, quasi-projective, proper, or smooth variety is a variety whose underlying
scheme or structure morphism has the corresponding property. Affine, projective, and
quasi-projective varieties admit the stated affine- or projective-space presentations.
-/
@[stacks 04L1] #check (@AlgebraicGeometry.affineVariety_iff :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k),
    AffineVariety X ↔ Variety X ∧ IsAffine X.left)

#check (@AlgebraicGeometry.affineVariety_iff_hasAffineSpacePresentation :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Variety X],
    AffineVariety X ↔ HasAffineSpacePresentation X)

#check (@AlgebraicGeometry.hasAffineSpacePresentation_iff :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k),
    HasAffineSpacePresentation X ↔
      ∃ n : ℕ, ∃ i : X.left ⟶ AffineSpaceOverField k n, IsAffineSpacePresentation X n i)

#check (@AlgebraicGeometry.projectiveVariety_iff :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k),
    ProjectiveVariety X ↔ Variety X ∧ Projective X.hom)

#check (@AlgebraicGeometry.projectiveVariety_iff_hProjective :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Variety X],
    ProjectiveVariety X ↔ HProjective X.hom)

#check (@AlgebraicGeometry.hProjective_iff :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S),
    HProjective f ↔
      ∃ (n : ℕ) (P : ProjectiveSpaceOver S n) (i : X ⟶ P.scheme),
        ProjectivePresentation f P.hom i)

#check (@AlgebraicGeometry.quasiProjectiveVariety_iff :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k),
    QuasiProjectiveVariety X ↔ Variety X ∧ QuasiProjective X.hom)

#check (@AlgebraicGeometry.quasiProjectiveVariety_iff_hQuasiProjective :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Variety X],
    QuasiProjectiveVariety X ↔ HQuasiProjective X.hom)

#check (@AlgebraicGeometry.hQuasiProjective_iff :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S},
    HQuasiProjective f ↔
      ∃ (n : ℕ) (P : ProjectiveSpaceOver S n) (i : X ⟶ P.scheme),
        QuasiCompact i ∧ IsImmersion i ∧ i ≫ P.hom = f)

#check (@AlgebraicGeometry.properVariety_iff :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k),
    ProperVariety X ↔ Variety X ∧ IsProper X.hom)

#check (@AlgebraicGeometry.smoothVariety_iff :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k),
    SmoothVariety X ↔ Variety X ∧ Smooth X.hom)
