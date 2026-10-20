/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.FittingIdeal

/-!
# Scalar presentations attached to differentials

For a module-valued homological complex `K`, a scalar `f`, and two degrees `i`, `j`, this file
owns the presentation map

`x ↦ (f • x, d i j x)`

and its quotient.  The construction is independent of a particular complex shape; chain and
cochain applications are specializations of this owner.  The associated Fitting ideal uses the
rank of the differential target and does not require the source term to be free.
@stack 0GST
-/

@[expose] public section

open CategoryTheory
open scoped FittingIdeal

noncomputable section

universe u v w

namespace HomologicalComplex.ScalarPresentation

variable {R : Type u} [CommRing R]
variable {ι : Type w} {c : ComplexShape ι}

/-- The scalar-differential presentation `x ↦ (f • x, d i j x)`. -/
@[stacks 0F7V "scalar-differential presentation map"]
abbrev map (f : R) (K : HomologicalComplex (ModuleCat.{v} R) c) (i j : ι) :
    K.X i →ₗ[R] K.X i × K.X j :=
  LinearMap.prod (f • LinearMap.id) (K.d i j).hom

/-- The first coordinate of the scalar-differential presentation is multiplication by the
scalar. -/
@[simp]
theorem fst_comp_map (f : R) (K : HomologicalComplex (ModuleCat.{v} R) c) (i j : ι) :
    (LinearMap.fst R (K.X i) (K.X j)).comp (map f K i j) =
      f • (LinearMap.id : K.X i →ₗ[R] K.X i) := sorry

/-- The second coordinate of the scalar-differential presentation is the differential. -/
@[simp]
theorem snd_comp_map (f : R) (K : HomologicalComplex (ModuleCat.{v} R) c) (i j : ι) :
    (LinearMap.snd R (K.X i) (K.X j)).comp (map f K i j) = (K.d i j).hom := sorry

/-- Evaluation of the scalar-differential presentation. -/
@[simp]
theorem map_apply (f : R) (K : HomologicalComplex (ModuleCat.{v} R) c)
    (i j : ι) (x : K.X i) : map f K i j x = (f • x, K.d i j x) := sorry

/-- The module presented by the scalar-differential map. -/
@[stacks 0F7V "scalar-differential presentation quotient"]
abbrev quotient (f : R) (K : HomologicalComplex (ModuleCat.{v} R) c) (i j : ι) :=
  (K.X i × K.X j) ⧸ LinearMap.range (map f K i j)

/-- The canonical projection onto the scalar-differential presentation quotient. -/
def mkQ (f : R) (K : HomologicalComplex (ModuleCat.{v} R) c) (i j : ι) :
    K.X i × K.X j →ₗ[R] quotient f K i j :=
  Submodule.mkQ (LinearMap.range (map f K i j))

/-- The presentation quotient map sends an element to its quotient class. -/
@[simp]
theorem mkQ_apply (f : R) (K : HomologicalComplex (ModuleCat.{v} R) c)
    (i j : ι) (x : K.X i × K.X j) :
    mkQ f K i j x = Submodule.Quotient.mk x := sorry

/-- A scalar-differential presentation quotient is finite when both target-product factors are
finite. -/
instance quotientFinite (f : R) (K : HomologicalComplex (ModuleCat.{v} R) c) (i j : ι)
    [Module.Finite R (K.X i)] [Module.Finite R (K.X j)] :
    Module.Finite R (quotient f K i j) := sorry

/-- The determinantal ideal of a scalar-differential presentation, indexed by the finite-free
rank of the differential target. -/
@[stacks 0F7V "determinantal ideal of a scalar-differential presentation"]
def fittingIdeal (f : R) (K : HomologicalComplex (ModuleCat.{v} R) c) (i j : ι)
    [Module.Finite R (K.X i)] [Module.Free R (K.X j)] [Module.Finite R (K.X j)] :
    Ideal R :=
  Fit[R]_(Module.finrank R (K.X j))(quotient f K i j)

/-- Berthelot-Ogus notation for the determinantal ideal of the scalar presentation in
consecutive cochain degrees.  It elaborates uniformly for both `ℕ`- and `ℤ`-indexed complexes. -/
scoped[BerthelotOgus] notation "I[" f "]_(" i ")(" K ")" =>
  HomologicalComplex.ScalarPresentation.fittingIdeal f K i (i + 1)

/-- The target automorphism which multiplies the first presentation coordinate by a unit and
fixes the differential coordinate. -/
abbrev unitTargetEquiv (u : Rˣ) (K : HomologicalComplex (ModuleCat.{v} R) c) (i j : ι) :
    (ModuleCat.carrier (K.X i) × ModuleCat.carrier (K.X j)) ≃ₗ[R]
      (ModuleCat.carrier (K.X i) × ModuleCat.carrier (K.X j)) :=
  (LinearEquiv.smulOfUnit (R := R) (M := K.X i) u).prodCongr
    (LinearEquiv.refl R (K.X j))

/-- The unit-rescaling target equivalence acts coordinatewise. -/
@[simp]
theorem unitTargetEquiv_apply (u : Rˣ) (K : HomologicalComplex (ModuleCat.{v} R) c)
    (i j : ι) (x : K.X i) (y : K.X j) :
    unitTargetEquiv u K i j (x, y) = ((u : R) • x, y) := sorry

/-- Rescaling the first target coordinate by `u` carries the presentation for `f` to the
presentation for `(u : R) * f`. -/
theorem unitTargetEquiv_map (f : R) (u : Rˣ)
    (K : HomologicalComplex (ModuleCat.{v} R) c) (i j : ι) (x : K.X i) :
    unitTargetEquiv u K i j (map f K i j x) = map ((u : R) * f) K i j x := sorry

/-- Rescaling the first target coordinate by a unit carries the range of one scalar presentation
onto the range of the rescaled presentation. -/
theorem range_unitTargetEquiv (f : R) (u : Rˣ)
    (K : HomologicalComplex (ModuleCat.{v} R) c) (i j : ι) :
    (LinearMap.range (map f K i j)).map (unitTargetEquiv u K i j).toLinearMap =
      LinearMap.range (map ((u : R) * f) K i j) := sorry

/-- Multiplying the presentation scalar by a unit induces a canonical equivalence of presentation
quotients. -/
noncomputable def quotientEquivUnitMul (f : R) (u : Rˣ)
    (K : HomologicalComplex (ModuleCat.{v} R) c) (i j : ι) :
    quotient f K i j ≃ₗ[R] quotient ((u : R) * f) K i j :=
  Submodule.Quotient.equiv
    (LinearMap.range (map f K i j))
    (LinearMap.range (map ((u : R) * f) K i j))
    (unitTargetEquiv u K i j)
    (range_unitTargetEquiv f u K i j)

/-- The quotient equivalence induced by unit rescaling acts on representatives by rescaling the
first coordinate. -/
@[simp]
theorem quotientEquivUnitMul_mk (f : R) (u : Rˣ)
    (K : HomologicalComplex (ModuleCat.{v} R) c) (i j : ι) (x : K.X i × K.X j) :
    quotientEquivUnitMul f u K i j (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (unitTargetEquiv u K i j x) := sorry

/-- Multiplying the scalar by a unit does not change a scalar-presentation determinantal ideal. -/
@[stacks 0GST "unit invariance of a scalar-presentation determinantal ideal"]
theorem fittingIdeal_unit_mul (f : R) (u : Rˣ)
    (K : HomologicalComplex (ModuleCat.{v} R) c) (i j : ι)
    [Module.Finite R (K.X i)] [Module.Free R (K.X j)] [Module.Finite R (K.X j)] :
    fittingIdeal f K i j = fittingIdeal ((u : R) * f) K i j := sorry

/-- The component of a strict complex isomorphism as a linear equivalence. -/
abbrev componentEquiv {K L : HomologicalComplex (ModuleCat.{v} R) c}
    (e : K ≅ L) (i : ι) : K.X i ≃ₗ[R] L.X i :=
  ((HomologicalComplex.eval (ModuleCat.{v} R) c i).mapIso e).toLinearEquiv

/-- The product of two components of a strict complex isomorphism. -/
abbrev targetEquiv {K L : HomologicalComplex (ModuleCat.{v} R) c}
    (e : K ≅ L) (i j : ι) :
    (ModuleCat.carrier (K.X i) × ModuleCat.carrier (K.X j)) ≃ₗ[R]
      (ModuleCat.carrier (L.X i) × ModuleCat.carrier (L.X j)) :=
  (componentEquiv e i).prodCongr (componentEquiv e j)

/-- A strict complex isomorphism intertwines scalar-differential presentation maps. -/
theorem targetEquiv_map (f : R)
    {K L : HomologicalComplex (ModuleCat.{v} R) c} (e : K ≅ L)
    (i j : ι) (x : K.X i) :
    targetEquiv e i j (map f K i j x) =
      map f L i j (componentEquiv e i x) := sorry

/-- A strict complex isomorphism carries the range of one scalar-differential presentation onto
the other. -/
theorem range_targetEquiv (f : R)
    {K L : HomologicalComplex (ModuleCat.{v} R) c} (e : K ≅ L) (i j : ι) :
    (LinearMap.range (map f K i j)).map (targetEquiv e i j).toLinearMap =
      LinearMap.range (map f L i j) := sorry

/-- A strict complex isomorphism induces an equivalence of scalar-differential presentation
quotients. -/
noncomputable def quotientEquivOfIso (f : R)
    {K L : HomologicalComplex (ModuleCat.{v} R) c} (e : K ≅ L) (i j : ι) :
    quotient f K i j ≃ₗ[R] quotient f L i j :=
  Submodule.Quotient.equiv
    (LinearMap.range (map f K i j))
    (LinearMap.range (map f L i j))
    (targetEquiv e i j)
    (range_targetEquiv f e i j)

/-- The quotient equivalence induced by a strict complex isomorphism acts on representatives by
the product of its degree components. -/
@[simp]
theorem quotientEquivOfIso_mk (f : R)
    {K L : HomologicalComplex (ModuleCat.{v} R) c} (e : K ≅ L)
    (i j : ι) (x : K.X i × K.X j) :
    quotientEquivOfIso f e i j (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (targetEquiv e i j x) := sorry

/-- The inverse quotient equivalence induced by a strict complex isomorphism acts on
representatives by the inverse product equivalence. -/
@[simp]
theorem quotientEquivOfIso_symm_mk (f : R)
    {K L : HomologicalComplex (ModuleCat.{v} R) c} (e : K ≅ L)
    (i j : ι) (x : L.X i × L.X j) :
    (quotientEquivOfIso f e i j).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((targetEquiv e i j).symm x) := sorry

/-- Strict complex isomorphisms preserve scalar-differential determinantal ideals. -/
theorem fittingIdeal_eq_of_iso (f : R)
    {K L : HomologicalComplex (ModuleCat.{v} R) c} (e : K ≅ L) (i j : ι)
    [Module.Finite R (K.X i)] [Module.Free R (K.X j)] [Module.Finite R (K.X j)]
    [Module.Finite R (L.X i)] [Module.Free R (L.X j)] [Module.Finite R (L.X j)] :
    fittingIdeal f K i j = fittingIdeal f L i j := sorry

end HomologicalComplex.ScalarPresentation
