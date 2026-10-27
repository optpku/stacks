/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.TypeValued.PushoutComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/-- The quotient functor sends a pushout of schemes along a thickening and an
affine morphism to a pullback of sets via its natural restriction comparison. -/
theorem pushoutComparison_bijective {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {Z Z' Y Y' : SchemeOver B} (i : Z ⟶ Z') (g : Z ⟶ Y)
    (inl : Z' ⟶ Y') (inr : Y ⟶ Y')
    [IsThickening i.left.left] [IsAffineHom g.left.left]
    (H : IsPushout i g inl inr) :
    Function.Bijective (FunctorToTypes.pushoutComparison (functor f F) H.w) := sorry

/-- When the structural morphism is locally of finite presentation, the functor
of finitely presented quotients sends a pushout of schemes along a thickening
and an affine morphism to a pullback of sets via its restriction comparison. -/
theorem fpPushoutComparison_bijective {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [LocallyOfFinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] {Z Z' Y Y' : SchemeOver B} (i : Z ⟶ Z') (g : Z ⟶ Y)
    (inl : Z' ⟶ Y') (inr : Y ⟶ Y')
    [IsThickening i.left.left] [IsAffineHom g.left.left]
    (H : IsPushout i g inl inr) :
    Function.Bijective (FunctorToTypes.pushoutComparison (fpFunctor f F) H.w) := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
