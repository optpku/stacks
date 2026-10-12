/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# Morphisms of sheaves of modules from basiswise linearity

This module promotes an additive morphism between the underlying presheaves of two sheaves of
modules to a module-sheaf morphism when scalar linearity is known on a topological basis.
-/

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace
open TopologicalSpace.Opens

noncomputable section

universe u

namespace SheafOfModules

variable {X : TopCat.{u}}

/-- An additive morphism between the underlying presheaves of two sheaves of modules is linear on
`B` when its component over every member of `B` commutes with the scalar action. -/
def IsLinearOnBasis
    {R : TopCat.Sheaf RingCat.{u} X} (M N : SheafOfModules.{u} R)
    (B : Set (Opens X)) (f : M.val.presheaf ⟶ N.val.presheaf) : Prop :=
  ∀ (U : Opens X), U ∈ B → ∀ (r : R.obj.obj (op U)) (m : M.val.presheaf.obj (op U)),
    f.app (op U) (r • m) = r • f.app (op U) m

/-- An additive morphism between sheaves of modules is linear on every open when it is linear on
a topological basis. -/
theorem linear_of_linearOnBasis
    {R : TopCat.Sheaf RingCat.{u} X} (M N : SheafOfModules.{u} R)
    (f : M.val.presheaf ⟶ N.val.presheaf)
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (h_linear : IsLinearOnBasis M N B f)
    (U : Opens X) (r : R.obj.obj (op U)) (m : M.val.presheaf.obj (op U)) :
    f.app (op U) (r • m) = r • f.app (op U) m := sorry

/-- The inverse of an additive presheaf isomorphism is linear on the same basis whenever its
forward map is linear there. -/
theorem IsLinearOnBasis.isoInv
    {R : TopCat.Sheaf RingCat.{u} X} {M N : SheafOfModules.{u} R}
    {B : Set (Opens X)} {e : M.val.presheaf ≅ N.val.presheaf}
    (h_linear : IsLinearOnBasis M N B e.hom) :
    IsLinearOnBasis N M B e.inv := sorry

/-- Lift an additive presheaf morphism to a morphism of sheaves of modules when it is linear on a
topological basis. -/
def homOfLinearOnBasis
    {R : TopCat.Sheaf RingCat.{u} X} (M N : SheafOfModules.{u} R)
    (f : M.val.presheaf ⟶ N.val.presheaf)
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (h_linear : IsLinearOnBasis M N B f) :
    M ⟶ N :=
  ⟨PresheafOfModules.homMk f
    (fun U => linear_of_linearOnBasis M N f hB h_linear U.unop)⟩

/-- Forgetting the module structure from `homOfLinearOnBasis` recovers the supplied additive
presheaf morphism. -/
@[simp]
theorem homOfLinearOnBasis_toPresheaf
    {R : TopCat.Sheaf RingCat.{u} X} (M N : SheafOfModules.{u} R)
    (f : M.val.presheaf ⟶ N.val.presheaf)
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (h_linear : IsLinearOnBasis M N B f) :
    (PresheafOfModules.toPresheaf R.obj).map (homOfLinearOnBasis M N f hB h_linear).val = f := sorry

/-- The morphisms lifted from the two directions of a basis-linear additive isomorphism satisfy
the first inverse law. -/
theorem homOfLinearOnBasis_hom_inv_id
    {R : TopCat.Sheaf RingCat.{u} X} (M N : SheafOfModules.{u} R)
    (e : M.val.presheaf ≅ N.val.presheaf)
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (h_linear : IsLinearOnBasis M N B e.hom) :
    homOfLinearOnBasis M N e.hom hB h_linear ≫
      homOfLinearOnBasis N M e.inv hB h_linear.isoInv = 𝟙 M := sorry

/-- The morphisms lifted from the two directions of a basis-linear additive isomorphism satisfy
the second inverse law. -/
theorem homOfLinearOnBasis_inv_hom_id
    {R : TopCat.Sheaf RingCat.{u} X} (M N : SheafOfModules.{u} R)
    (e : M.val.presheaf ≅ N.val.presheaf)
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (h_linear : IsLinearOnBasis M N B e.hom) :
    homOfLinearOnBasis N M e.inv hB h_linear.isoInv ≫
      homOfLinearOnBasis M N e.hom hB h_linear = 𝟙 N := sorry

/-- Lift a basis-linear additive presheaf isomorphism to an isomorphism of sheaves of modules. -/
def isoOfLinearOnBasis
    {R : TopCat.Sheaf RingCat.{u} X} (M N : SheafOfModules.{u} R)
    (e : M.val.presheaf ≅ N.val.presheaf)
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (h_linear : IsLinearOnBasis M N B e.hom) :
    M ≅ N where
  hom := homOfLinearOnBasis M N e.hom hB h_linear
  inv := homOfLinearOnBasis N M e.inv hB h_linear.isoInv
  hom_inv_id := homOfLinearOnBasis_hom_inv_id M N e hB h_linear
  inv_hom_id := homOfLinearOnBasis_inv_hom_id M N e hB h_linear

/-- Forgetting the forward map of `isoOfLinearOnBasis` recovers the supplied additive presheaf
morphism. -/
@[simp]
theorem isoOfLinearOnBasis_toSheaf_hom
    {R : TopCat.Sheaf RingCat.{u} X} (M N : SheafOfModules.{u} R)
    (e : M.val.presheaf ≅ N.val.presheaf)
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (h_linear : IsLinearOnBasis M N B e.hom) :
    ((SheafOfModules.toSheaf R).map (isoOfLinearOnBasis M N e hB h_linear).hom).hom = e.hom := sorry

/-- Forgetting the inverse map of `isoOfLinearOnBasis` recovers the supplied additive presheaf
morphism. -/
@[simp]
theorem isoOfLinearOnBasis_toSheaf_inv
    {R : TopCat.Sheaf RingCat.{u} X} (M N : SheafOfModules.{u} R)
    (e : M.val.presheaf ≅ N.val.presheaf)
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (h_linear : IsLinearOnBasis M N B e.hom) :
    ((SheafOfModules.toSheaf R).map (isoOfLinearOnBasis M N e hB h_linear).inv).hom = e.inv := sorry

end SheafOfModules
