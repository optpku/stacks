module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.ConstantPullback

/-!
# Constant `ZMod`-coefficient étale cohomology

This module defines the small-étale cohomology groups with constant cyclic
coefficients, their canonical scalar action, and contravariant pullback maps.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Small-étale cohomology `H^i(X, underline(ZMod m))` of the constant sheaf
associated to `ULift (ZMod m)`. -/
abbrev etaleHq_constantZMod (X : Scheme.{u}) (m i : ℕ) : Type u :=
  (Sheaf.functorH X.smallEtaleTopology i).obj
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} (ZMod m))))

/-- The constant-sheaf presentation of `etaleHq_constantZMod X m i`. -/
theorem etaleHq_constantZMod_eq (X : Scheme.{u}) (m i : ℕ) :
    etaleHq_constantZMod X m i =
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} (ZMod m)))).H i :=
  sorry

/-- Every class in `H^i(X, underline(ZMod m))` is annihilated by `m`. -/
theorem etaleHq_constantZMod_nsmul_eq_zero {X : Scheme.{u}} {m i : ℕ}
    (x : etaleHq_constantZMod X m i) : m • x = 0 :=
  sorry

/-- The canonical `ZMod m`-module structure on constant-coefficient étale
cohomology. -/
instance instModule_etaleHq_constantZMod {X : Scheme.{u}} {m i : ℕ} :
    Module (ZMod m) (etaleHq_constantZMod X m i) :=
  AddCommGroup.zmodModule etaleHq_constantZMod_nsmul_eq_zero

/-- The `ZMod m`-linear pullback induced by a scheme morphism
`f : X ⟶ Y`. -/
def etaleHq_constantZModMap {X Y : Scheme.{u}} (f : X ⟶ Y) (m i : ℕ) :
    etaleHq_constantZMod Y m i →ₗ[ZMod m] etaleHq_constantZMod X m i :=
  (etaleHq_constant_pullback f (AddCommGrpCat.of (ULift.{u} (ZMod m))) i).hom.toZModLinearMap m

/-- The underlying additive map of the constant-coefficient linear pullback. -/
theorem etaleHq_constantZModMap_addHom {X Y : Scheme.{u}} (f : X ⟶ Y) (m i : ℕ) :
    (etaleHq_constantZModMap f m i :
        etaleHq_constantZMod Y m i →+ etaleHq_constantZMod X m i) =
      (etaleHq_constant_pullback f (AddCommGrpCat.of (ULift.{u} (ZMod m))) i).hom :=
  sorry

end AlgebraicGeometry.Scheme.Hom
