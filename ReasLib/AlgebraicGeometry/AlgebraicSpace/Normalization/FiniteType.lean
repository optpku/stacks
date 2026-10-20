/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidueField.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.QuasiCompact

/-!
# Finite fibres and residue-field extensions of relative normalization

For a universally closed quasi-separated morphism of algebraic spaces which is
locally of finite type and has affine target, the relative-normalization
morphism has finite point-set fibres and finite residue-field extensions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace.Hom

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The relative normalization of a universally closed quasi-separated locally
finite type morphism of algebraic spaces into an affine target has finite
point-set fibres. -/
theorem fromNormalization_fiberFinite {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [UniversallyClosed f] [QuasiSeparated f] [LocallyOfFiniteType f]
    [IsAffine Y] (y : Points Y) :
    Set.Finite (fiberOver (fromNormalization f) y) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a universally closed quasi-separated locally finite type morphism into
an affine algebraic space, each residue field along a fibre of the relative
normalization is finite as a module over the residue field of the base point. -/
instance instModuleFiniteResidueFieldFromNormalization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [UniversallyClosed f] [QuasiSeparated f] [LocallyOfFiniteType f]
    [IsAffine Y] (y : Points Y) (y' : fiberOver (fromNormalization f) y) :
    Module.Finite (Y.residueField y) ((normalization f).residueField y') :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
