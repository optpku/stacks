/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.CompletionAlong
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffinePresentation
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.McQuillan
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffineTypes

/-!
# Affine properties of completion along a closed subset

Completion preserves affineness, McQuillan and Noetherian properties. It preserves
countable indexing and adic* when the complement of the closed subset is compact.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace (Points)

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.Recompletion

/-- Completion of an affine formal algebraic space along a closed subset of its
reduction is affine. -/
theorem isAffine {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X]
    [AffineFormalAlgebraicSpace.IsAffine X]
    (R : ReductionData X) (T : Closeds (Points R.space)) :
    AffineFormalAlgebraicSpace.IsAffine (functor R T) :=
  sorry

/-- Completion of a McQuillan affine formal algebraic space along a closed
subset of its reduction is McQuillan. -/
theorem isMcQuillanAffine {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X]
    [AffineFormalAlgebraicSpace.IsAffine X]
    [IsMcQuillanAffine X]
    (R : ReductionData X) (T : Closeds (Points R.space)) :
    IsMcQuillanAffine (functor R T) :=
  sorry

/-- Completion of a countably indexed affine formal algebraic space is countably
indexed when the closed subset has compact complement in its reduction. -/
theorem isCountablyIndexedAffine {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X]
    [AffineFormalAlgebraicSpace.IsCountablyIndexedAffine X]
    (R : ReductionData X) (T : Closeds (Points R.space))
    (hT : IsCompact (T.compl : Set (Points R.space))) :
    AffineFormalAlgebraicSpace.IsCountablyIndexedAffine (functor R T) :=
  sorry

/-- Completion of an adic* affine formal algebraic space is adic* when the
closed subset has compact complement in its reduction. -/
theorem isAdicStarAffine {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X]
    [AffineFormalAlgebraicSpace.IsAffine X]
    [IsAdicStarAffine X]
    (R : ReductionData X) (T : Closeds (Points R.space))
    (hT : IsCompact (T.compl : Set (Points R.space))) :
    IsAdicStarAffine (functor R T) :=
  sorry

/-- Completion of a Noetherian affine formal algebraic space along a closed
subset of its reduction is Noetherian. -/
theorem isNoetherianAffine {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X]
    [AffineFormalAlgebraicSpace.IsAffine X]
    [IsNoetherianAffine X]
    (R : ReductionData X) (T : Closeds (Points R.space)) :
    IsNoetherianAffine (functor R T) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.Recompletion
