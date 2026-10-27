/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.BaseChange.RightAdjoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.StructureSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.TorDimension.Relative
public import ReasLib.CategoryTheory.DerivedCategory.Bounded

/-! # Twisted right-adjoint base change over affine bases -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}

/-- For a Tor-independent cartesian square of algebraic spaces with affine bases
and a proper flat finitely presented vertical morphism, the canonical twisted
right-adjoint base-change map is invertible on every quasi-coherent complex. -/
theorem twistedMap_app_isIso_of_flat
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsAffine Y] [IsAffine Y'] [Proper f] [Flat f] [FinitePresentation f]
    [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    (sq : IsPullback g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g))
    (K : DerivedQCoh Y) :
    IsIso ((twistedMap g' f' f g sq a a' fAdj f'Adj hTor).app K) := sorry

/-- For a Tor-independent cartesian square of algebraic spaces with affine bases,
a Noetherian target, and a proper perfect vertical morphism, the canonical twisted
right-adjoint base-change map is invertible on every quasi-coherent complex. -/
theorem twistedMap_app_isIso_of_perfect
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsAffine Y] [IsAffine Y'] [Proper f] [Perfect f] [IsNoetherian Y]
    [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    (sq : IsPullback g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g))
    (K : DerivedQCoh Y) :
    IsIso ((twistedMap g' f' f g sq a a' fAdj f'Adj hTor).app K) := sorry

/-- For a Tor-independent cartesian square of algebraic spaces with affine bases,
a Noetherian target, a proper vertical morphism, and finite Tor dimension of the
base morphism, the canonical twisted right-adjoint base-change map is invertible
on every bounded-below quasi-coherent complex. -/
theorem twistedMap_app_isIso_of_finiteTorDimension
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsAffine Y] [IsAffine Y'] [Proper f] [IsNoetherian Y]
    [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    (sq : IsPullback g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g))
    (K : DerivedQCoh Y) (hK : K.obj.IsBoundedBelow)
    (h_finiteTor : ModuleDerived.HasFiniteTorDimensionOver g (DerivedQCoh.structureSheaf Y').obj) :
    IsIso ((twistedMap g' f' f g sq a a' fAdj f'Adj hTor).app K) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange
