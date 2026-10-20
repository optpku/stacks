/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Specialization.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.RelativeFunction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyCatenary
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Degree

/-!
# Equal δ-dimension morphisms of integral algebraic spaces

A morphism of good integral algebraic spaces of equal relative dimension either
factors through a proper closed subspace or is dominant with finite generic
residue-field extension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- A base-compatible morphism between integral algebraic spaces whose structure
morphisms are quasi-separated and locally of finite type over a quasi-separated,
universally catenary base either factors through a proper closed subspace or is
dominant with finite generic residue-field extension, provided their relative
dimension functions agree at generic points. -/
theorem factorsThrough_properClosed_or_finiteResidueFieldExtension
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) (pY : Y ⟶ B)
    [QuasiSeparated pX] [LocallyOfFiniteType pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    {x : Points X} {y : Points Y}
    (hx : x ∈ genericPoints X) (hy : y ∈ genericPoints Y)
    (hdim : AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction pX δ x = AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction pY δ y) :
    (∃ Z : ClosedSubspace Y,
        Z.pointsSet ≠ Set.univ ∧ ∃ g : X ⟶ Z.X, g ≫ Z.ι = f) ∨
      (Dominant f ∧ FiniteResidueFieldExtensionAt f x) :=
  sorry

/-- A dominant base-compatible morphism between integral algebraic spaces whose
structure morphisms are quasi-separated and locally of finite type over a
quasi-separated, universally catenary base has finite generic residue-field
extension if their relative dimension functions agree at generic points. -/
theorem finiteResidueFieldExtension_of_eq_deltaDimension
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) (pY : Y ⟶ B)
    [QuasiSeparated pX] [LocallyOfFiniteType pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hf : f ≫ pY = pX) [Dominant f]
    {x : Points X} {y : Points Y}
    (hx : x ∈ genericPoints X) (hy : y ∈ genericPoints Y)
    (hdim : AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction pX δ x = AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction pY δ y) :
    FiniteResidueFieldExtension f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
