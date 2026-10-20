module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StructureSheaf.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Picard.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver.MorphismProperty
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricallyIntegralFibres

/-!
# Separatedness of the relative Picard sheaf

The relative Picard sheaf of a flat, proper, finitely presented morphism with
universally preserved structure sheaf and integral geometric fibres has closed diagonal.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativePicard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The relative Picard sheaf of a flat, proper, finitely presented morphism with
integral geometric fibres has closed diagonal if the canonical structure-sheaf map
is an isomorphism after every scheme-valued base change. -/
theorem separated (f : X ⟶ B) [Flat f] [Proper f] [FinitePresentation f]
    [Hom.IsIsoBaseChangeStructurePushforward f]
    [Hom.HasIntegralGeometricFibres f] :
    SchemeOver.IsClosedImmersion (CategoryTheory.Limits.diag (picardFunctor f).obj) := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativePicard
