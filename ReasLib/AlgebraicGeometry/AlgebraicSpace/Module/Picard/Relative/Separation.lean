module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Picard.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StructureSheaf.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper

/-!
# Local separatedness of the relative Picard functor

The relative Picard diagonal is representable by immersions under flatness,
finite presentation, properness, and universal preservation of the structure sheaf.
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

end AlgebraicGeometry.AlgebraicSpace.RelativePicard
