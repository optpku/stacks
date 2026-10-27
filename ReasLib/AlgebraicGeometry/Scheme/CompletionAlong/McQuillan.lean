/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CompletionAlong
public import ReasLib.AlgebraicGeometry.FormalSpectrum.AffineCompletion
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.McQuillan

/-!
# McQuillan property of affine scheme completions

Completion of an affine scheme along an arbitrary closed subset is a McQuillan
affine formal algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- Completion of an affine spectrum agrees with its affine completion functor. -/
theorem completionAlong_eq_affineCompletionAlong {S : Scheme.{u}} {A : Type u}
    [CommRing A] (structureHom : Spec (.of A) ⟶ S)
    (T : Closeds (Spec (.of A))) :
    completionAlong (Over.mk structureHom) T =
      affineCompletionAlong structureHom T :=
  sorry

/-- Completion of an affine scheme over any base along a closed subset is a
McQuillan affine formal algebraic space. -/
instance instIsMcQuillanAffine_completionAlong {S : Scheme.{u}} (X : Over S)
    [IsAffine X.left] (T : Closeds X.left) :
    AlgebraicGeometry.FormalAlgebraicSpace.IsMcQuillanAffine (completionAlong X T) :=
  sorry

/-- Completion along a closed subset of an affine spectrum over any base is a
McQuillan affine formal algebraic space. -/
instance isMcQuillanAffine_affineCompletionAlong {S : Scheme.{u}} {A : Type u}
    [CommRing A] (structureHom : Spec (.of A) ⟶ S)
    (T : Closeds (Spec (.of A))) :
    AlgebraicGeometry.FormalAlgebraicSpace.IsMcQuillanAffine
      (affineCompletionAlong structureHom T) :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
