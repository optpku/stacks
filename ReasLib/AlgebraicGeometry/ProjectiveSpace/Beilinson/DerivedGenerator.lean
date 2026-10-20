/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Beilinson.Generator
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn

/-!
# The derived Beilinson generator on projective space

This file places the finite coproduct of the standard negative twisting sheaves in degree zero
as an object with quasicoherent cohomology.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- The degree-zero derived object associated to the Beilinson generator has
quasicoherent cohomology. -/
theorem derivedBeilinsonGenerator_mem (A : Type u) [CommRing A] (n : ℕ) :
    Scheme.ModuleDerived.quasicoherentProperty (scheme A n)
      ((DerivedCategory.singleFunctor (scheme A n).Modules 0).obj
        (beilinsonGenerator A n)) := sorry

/-- The finite coproduct `𝒪 ⊕ 𝒪(-1) ⊕ ⋯ ⊕ 𝒪(-n)`, placed in degree zero as an
object with quasicoherent cohomology on `ℙⁿ_A`. -/
noncomputable def derivedBeilinsonGenerator (A : Type u) [CommRing A] (n : ℕ) :
    Scheme.ModuleDerived.Quasicoherent (scheme A n) :=
  ⟨(DerivedCategory.singleFunctor (scheme A n).Modules 0).obj
      (beilinsonGenerator A n),
    derivedBeilinsonGenerator_mem A n⟩

/-- The underlying derived object of `derivedBeilinsonGenerator A n` is the
degree-zero single object on `beilinsonGenerator A n`. -/
theorem derivedBeilinsonGenerator_obj (A : Type u) [CommRing A] (n : ℕ) :
    (derivedBeilinsonGenerator A n).obj =
      (DerivedCategory.singleFunctor (scheme A n).Modules 0).obj
        (beilinsonGenerator A n) := sorry

end AlgebraicGeometry.ProjectiveSpace
