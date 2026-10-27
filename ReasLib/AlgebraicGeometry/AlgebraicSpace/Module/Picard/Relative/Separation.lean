/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.QuasiCompactImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Picard.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StructureSheaf.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper

/-!
# Separation and quasi-compactness of the relative Picard diagonal

The relative Picard diagonal is representable by quasi-compact immersions under
flatness, finite presentation, properness, and universal preservation of the
structure sheaf. A representing morphism is locally separated and quasi-separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativePicard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- For a flat, finitely presented, proper morphism preserving the structure sheaf
after every scheme-valued base change, the relative Picard diagonal is
representable by immersions. -/
theorem locallySeparated (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f]
    [Hom.IsIsoBaseChangeStructurePushforward f] :
    IsImmersionOnSchemesOver (Limits.diag (picardFunctor f).obj) := sorry

/-- A morphism representing the relative Picard functor of a flat, finitely
presented, proper morphism preserving the structure sheaf after every
scheme-valued base change is locally separated. -/
theorem locallySeparated_of_representable (f : X ⟶ B)
    [Flat f] [FinitePresentation f] [Proper f]
    [Hom.IsIsoBaseChangeStructurePushforward f] {Y : AlgebraicSpace S}
    {π : Y ⟶ B} (e : (picardFunctor f).obj ≅ yonedaOver π) :
    LocallySeparated π := sorry

/-- For a flat, finitely presented, proper morphism preserving the structure sheaf
after every scheme-valued base change, the relative Picard diagonal is
representable by quasi-compact immersions. -/
theorem isQuasiCompactImmersion_diagonal (f : X ⟶ B)
    [Flat f] [FinitePresentation f] [Proper f]
    [Hom.IsIsoBaseChangeStructurePushforward f] :
    IsQuasiCompactImmersionOnSchemesOver (Limits.diag (picardFunctor f).obj) := sorry

/-- A morphism representing the relative Picard functor of a flat, finitely
presented, proper morphism preserving the structure sheaf after every
scheme-valued base change is locally separated and quasi-separated. -/
theorem isQuasiCompactImmersion_diagonal_of_representable (f : X ⟶ B)
    [Flat f] [FinitePresentation f] [Proper f]
    [Hom.IsIsoBaseChangeStructurePushforward f] {Y : AlgebraicSpace S}
    {π : Y ⟶ B} (e : (picardFunctor f).obj ≅ yonedaOver π) :
    LocallySeparated π ∧ QuasiSeparated π := sorry

/-- For a flat, finitely presented, proper morphism preserving the structure sheaf
after every scheme-valued base change, the relative Picard diagonal is
quasi-compact. -/
theorem quasiSeparated (f : X ⟶ B)
    [Flat f] [FinitePresentation f] [Proper f]
    [Hom.IsIsoBaseChangeStructurePushforward f] :
    IsQuasiCompactOnSchemesOver (Limits.diag (picardFunctor f).obj) := sorry

/-- A morphism representing the relative Picard functor of a flat, finitely
presented, proper morphism preserving the structure sheaf after every
scheme-valued base change is quasi-separated. -/
theorem quasiSeparated_of_representable (f : X ⟶ B)
    [Flat f] [FinitePresentation f] [Proper f]
    [Hom.IsIsoBaseChangeStructurePushforward f] {Y : AlgebraicSpace S}
    {π : Y ⟶ B} (e : (picardFunctor f).obj ≅ yonedaOver π) :
    QuasiSeparated π := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativePicard
