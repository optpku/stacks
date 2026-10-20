/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback.Scheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Affine criteria for absolute separatedness

Absolute separatedness of an algebraic space is characterized by closed immersions on affine
scheme tests, or by affine fibre products with surjective tensor maps on global sections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Fibre products of morphisms from affine schemes to `X` are affine, and the induced
`ℤ`-tensor map on global sections is surjective. -/
def forallAffinePullbackAffineSurjective {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop :=
  ∀ (U V : Over S) [IsAffine U.left] [IsAffine V.left]
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X),
    IsAffine (schemePullback f g).left ∧ Function.Surjective (schemePullback.tensorHom f g).hom

/-- `forallAffinePullbackAffineSurjective X` means that affine tests `U ⟶ X` and `V ⟶ X` have
affine fibre product with surjective tensor map on global sections. -/
theorem forallAffinePullbackAffineSurjective_iff {S : Scheme.{u}} (X : AlgebraicSpace S) :
    forallAffinePullbackAffineSurjective X ↔
      ∀ (U V : Over S) [IsAffine U.left] [IsAffine V.left]
        (f : ofOver U ⟶ X) (g : ofOver V ⟶ X),
        IsAffine (schemePullback f g).left ∧
          Function.Surjective (schemePullback.tensorHom f g).hom :=
  Iff.rfl

namespace forallAffinePullbackAffineSurjective

/-- The universal affine-scheme pullback condition witnesses
`forallAffinePullbackAffineSurjective X`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : ∀ (U V : Over S) [IsAffine U.left] [IsAffine V.left]
      (f : ofOver U ⟶ X) (g : ofOver V ⟶ X),
      IsAffine (schemePullback f g).left ∧
        Function.Surjective (schemePullback.tensorHom f g).hom) :
    forallAffinePullbackAffineSurjective X :=
  h

/-- If `forallAffinePullbackAffineSurjective X`, then the fibre product of morphisms from affine
schemes to `X` is affine with surjective tensor map on global sections. -/
theorem apply {S : Scheme.{u}} {X : AlgebraicSpace S} (h : forallAffinePullbackAffineSurjective X)
    {U V : Over S} [IsAffine U.left] [IsAffine V.left]
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X) :
    IsAffine (schemePullback f g).left ∧ Function.Surjective (schemePullback.tensorHom f g).hom :=
  h U V f g

end forallAffinePullbackAffineSurjective

/-- Fibre products of morphisms from affine schemes to `X` induce a closed immersion into the
absolute product of the underlying schemes. -/
def forallAffinePullbackClosedImmersion {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop :=
  ∀ (U V : Over S) [IsAffine U.left] [IsAffine V.left]
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X),
    IsClosedImmersion (schemePullback.toProd f g)

/-- `forallAffinePullbackClosedImmersion X` means that affine tests `U ⟶ X` and `V ⟶ X` have
comparison morphism `U ×_X V ⟶ U × V` a closed immersion. -/
theorem forallAffinePullbackClosedImmersion_iff {S : Scheme.{u}} (X : AlgebraicSpace S) :
    forallAffinePullbackClosedImmersion X ↔
      ∀ (U V : Over S) [IsAffine U.left] [IsAffine V.left]
        (f : ofOver U ⟶ X) (g : ofOver V ⟶ X),
        IsClosedImmersion (schemePullback.toProd f g) :=
  Iff.rfl

namespace forallAffinePullbackClosedImmersion

/-- The universal closed-immersion condition on affine tests witnesses
`forallAffinePullbackClosedImmersion X`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : ∀ (U V : Over S) [IsAffine U.left] [IsAffine V.left]
      (f : ofOver U ⟶ X) (g : ofOver V ⟶ X),
      IsClosedImmersion (schemePullback.toProd f g)) :
    forallAffinePullbackClosedImmersion X :=
  h

/-- If `forallAffinePullbackClosedImmersion X`, then the comparison of an affine test fibre
product to the absolute product is a closed immersion. -/
theorem apply {S : Scheme.{u}} {X : AlgebraicSpace S} (h : forallAffinePullbackClosedImmersion X)
    {U V : Over S} [IsAffine U.left] [IsAffine V.left]
    (f : ofOver U ⟶ X) (g : ofOver V ⟶ X) :
    IsClosedImmersion (schemePullback.toProd f g) :=
  h U V f g

end forallAffinePullbackClosedImmersion

namespace IsAbsolutelySeparated

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- An algebraic space is absolutely separated iff fibre products of morphisms from affine schemes
induce a closed immersion into the absolute product of the underlying schemes. -/
theorem iff_forallAffinePullbackClosedImmersion :
    IsAbsolutelySeparated X ↔ forallAffinePullbackClosedImmersion X :=
  sorry

/-- An algebraic space is absolutely separated iff fibre products of morphisms from affine schemes
are affine with surjective tensor map on global sections. -/
theorem iff_forallAffinePullbackAffineSurjective :
    IsAbsolutelySeparated X ↔ forallAffinePullbackAffineSurjective X :=
  sorry

/-- Absolute separatedness and the affine fibre-product condition with surjective tensor map on
global sections are equivalent. -/
theorem tfae : List.TFAE [IsAbsolutelySeparated X, forallAffinePullbackAffineSurjective X] :=
  List.tfae_cons_cons.mpr
    ⟨iff_forallAffinePullbackAffineSurjective X, List.tfae_singleton _⟩

end IsAbsolutelySeparated

end AlgebraicGeometry.AlgebraicSpace
