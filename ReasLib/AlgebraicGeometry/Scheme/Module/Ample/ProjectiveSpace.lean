/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery.ProjectiveSpace
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.Characterization
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.Power

/-!
# Projective-space presentations of high tensor powers of ample modules

This file relates ample invertible modules on schemes locally of finite type over a base to
immersions into finite relative projective spaces.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}

namespace IsAmple

/-- For a locally finite type morphism, every sufficiently high tensor power of an ample
invertible module is the pullback of the tautological module along an immersion over the base
into a finite relative projective space. -/
@[stacks 01VS]
theorem eventualProjectiveSpacePresentation
    [Invertible L] [IsAmple L] [LocallyOfFiniteType f] :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      ∃ (n : ℕ) (P : ProjectiveSpaceOver S n) (i : X ⟶ P.scheme),
        ∃ e : RingedSpace.TensorPower.sheaf L d ≅
            (Scheme.Modules.pullback i).obj P.tautologicalSheaf,
          IsImmersion i ∧ i ≫ P.hom = f := sorry

/-- Over an affine base, ampleness and relative ampleness of an invertible module are equivalent
to relative very ampleness of some or every sufficiently high positive tensor power, and to
presentations of such tensor powers by immersions into positive-dimensional relative projective
spaces. -/
theorem tfae_relative_of_finiteType_affineBase
    [Invertible L] [IsAffine S] [Scheme.Hom.FiniteType f] :
    List.TFAE [
      IsAmple L,
      RelativelyAmple f L,
      ∃ d : ℕ, 1 ≤ d ∧
        RelativelyVeryAmple f (RingedSpace.TensorPower.sheaf L d),
      ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
        RelativelyVeryAmple f (RingedSpace.TensorPower.sheaf L d),
      ∃ d : ℕ, 1 ≤ d ∧
        ∃ n : ℕ, 1 ≤ n ∧
          ∃ (P : ProjectiveSpaceOver S n) (i : X ⟶ P.scheme),
            ∃ e : RingedSpace.TensorPower.sheaf L d ≅
                (Scheme.Modules.pullback i).obj P.tautologicalSheaf,
              IsImmersion i ∧ i ≫ P.hom = f,
      ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
        ∃ n : ℕ, 1 ≤ n ∧
          ∃ (P : ProjectiveSpaceOver S n) (i : X ⟶ P.scheme),
            ∃ e : RingedSpace.TensorPower.sheaf L d ≅
                (Scheme.Modules.pullback i).obj P.tautologicalSheaf,
              IsImmersion i ∧ i ≫ P.hom = f] := sorry

end IsAmple

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.RelativelyAmple

variable {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}

/-- An invertible module for a finite-type morphism is relatively ample exactly when, locally on
the base, a positive tensor power is the pullback of the tautological module along an immersion
into a finite relative projective space. -/
@[stacks 02NR]
theorem iff_exists_openCover_projectiveSpacePresentation_of_finiteType
    [Scheme.Modules.Invertible L] [Scheme.Hom.FiniteType f] :
    RelativelyAmple f L ↔
      ∃ 𝒰 : Scheme.OpenCover.{u} S, ∀ j : 𝒰.I₀,
        ∃ d : ℕ, 1 ≤ d ∧
          ∃ (n : ℕ) (P : ProjectiveSpaceOver ((𝒰.f j).opensRange).toScheme n)
              (i : (f ⁻¹ᵁ (𝒰.f j).opensRange).toScheme ⟶ P.scheme),
            ∃ e : Scheme.Modules.restrict (RingedSpace.TensorPower.sheaf L d)
                ((f ⁻¹ᵁ (𝒰.f j).opensRange).ι) ≅
                  (Scheme.Modules.pullback i).obj P.tautologicalSheaf,
              IsImmersion i ∧ i ≫ P.hom = f ∣_ (𝒰.f j).opensRange := sorry

end AlgebraicGeometry.RelativelyAmple
