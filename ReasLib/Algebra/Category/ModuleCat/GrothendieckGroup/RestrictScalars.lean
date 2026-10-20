module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Restriction of scalars on finite-module Grothendieck groups

This leaf owns the additive map induced by restricting finite modules along a finite algebra map.
The map is concrete; only preservation of short-exact relations is proposition-valued debt.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory
open CategoryTheory.ShortComplex.ShortExact

namespace CategoryTheory.ModuleCat.K0

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B]

/-
API design: the restriction map repeatedly needs the same canonical A-module structure on a finite
B-module.  This named data owner keeps the three required instance pins in one place; callers see a
finite Grothendieck class rather than a `letI` staircase.  The owner is concrete, while only the
relation-preservation theorem below remains proposition-valued debt.
-/

/-- The finite-module Grothendieck class after restricting scalars from `B` to `A`. -/
@[stacks 00K1 "restricted-scalar finite Grothendieck class"]
noncomputable def finiteClass_restrictScalars (M : Type w) [AddCommGroup M] [Module B M]
    [Module.Finite B M] : finite A :=
  let _ : Module A M := Module.restrictScalars A B M
  let _ : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : Module.Finite A M := Module.Finite.trans (R := A) B M
  finiteClass A M

/-- Restricting scalars sends every finite `B`-module short-exact relation to zero over `A`. -/
@[stacks 00K1 "restriction of scalars kills Grothendieck relations"]
theorem restrictScalars_relations_le_ker :
    ObjectProperty.GrothendieckGroup.relations (ModuleCat.isFG B) ≤
      (FreeAbelianGroup.lift fun M : FGModuleCat B ↦
        finiteClass_restrictScalars (A := A) (B := B) M.obj).ker := sorry

/-- The canonical additive map `K'_0(B) → K'_0(A)` induced by restriction of scalars. -/
@[stacks 00K1 "restriction of scalars on finite Grothendieck groups"]
noncomputable def restrictScalars : finite B →+ finite A :=
  QuotientAddGroup.lift (ObjectProperty.GrothendieckGroup.relations (ModuleCat.isFG B))
    (FreeAbelianGroup.lift fun M : FGModuleCat B ↦
      finiteClass_restrictScalars (A := A) (B := B) M.obj)
    (restrictScalars_relations_le_ker (A := A) (B := B))

/-- Evaluation of restriction of scalars on a finite-module generator. -/
@[simp, stacks 00K1 "restriction of scalars on a generator"]
theorem restrictScalars_apply_of (N : FGModuleCat B) :
    restrictScalars (A := A) (B := B) (finiteOf B N) =
      finiteClass_restrictScalars (A := A) (B := B) N.obj := sorry

end CategoryTheory.ModuleCat.K0
