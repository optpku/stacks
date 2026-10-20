/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.LocallyProjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.GlobalSections.Abelian

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory
open CategoryTheory.DerivedCategory
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- On a quasi-compact and quasi-separated algebraic space, a derived quasicoherent module
whose cohomology sheaves have countable sections on affine étale charts has countable
perfect-tensor hypercohomology after every quasi-compact and quasi-separated étale restriction,
in every integer degree. -/
theorem tensorEtaleHypercohomologyCountable {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (K : DerivedQCoh X)
    (hK : ∀ (j : ℤ) (U : affineEtaleSite X),
      Countable
        (sectionModule ((DerivedCategory.homologyFunctor (Modules X) j).obj K.obj) U.obj))
    {U : AlgebraicSpace S} (f : U ⟶ X) [Etale f] [QuasiCompact f] [QuasiSeparated f]
    (E : ModuleDerived X) (hE : ModuleDerived.IsPerfect E) (i : ℤ) :
    Countable
      (cohomologyAb U
        ((restrictFunctorDerived f).obj ((DerivedTensor.Right.functor E).obj K.obj)) i) :=
  sorry

/-- On a quasi-compact and quasi-separated algebraic space, every extension group from a
perfect derived module to a derived quasicoherent module whose cohomology sheaves have
countable sections on affine étale charts is countable after every quasi-compact and
quasi-separated étale restriction, in every integer degree. -/
theorem restrictedExtCountable {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (K : DerivedQCoh X)
    (hK : ∀ (j : ℤ) (U : affineEtaleSite X),
      Countable
        (sectionModule ((DerivedCategory.homologyFunctor (Modules X) j).obj K.obj) U.obj))
    {U : AlgebraicSpace S} (f : U ⟶ X) [Etale f] [QuasiCompact f] [QuasiSeparated f]
    (E : ModuleDerived X) (hE : ModuleDerived.IsPerfect E) (i : ℤ) :
    Countable
      (Ext⁽i⁾((restrictFunctorDerived f).obj E,
        (restrictFunctorDerived f).obj K.obj)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
