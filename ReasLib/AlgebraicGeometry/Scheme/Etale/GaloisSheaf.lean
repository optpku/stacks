/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.StalkFunctor

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Action.ModuleCat
open AlgebraicGeometry

noncomputable section

universe u

namespace GaloisCohomology

variable (K Ksep : Type u) [Field K] [Field Ksep]
  [Algebra K Ksep] [IsSepClosure K Ksep]

/-- Sections over an étale scheme are equivariant functions from its separable point fiber. -/
abbrev discreteSheafSections (M : DiscreteModuleCat ℤ (Gal(Ksep / K)))
    (U : (Spec (.of K)).Etale) :
    AddSubgroup ((etalePoint K Ksep).fiber.obj U → M.obj.V) where
  carrier := { section_ | ∀ sigma point,
    section_ ((etaleFiberAction K Ksep sigma).app U point) =
      (M.obj.ρ sigma).hom (section_ point) }
  zero_mem' := by
    intro sigma point
    exact (map_zero (M.obj.ρ sigma).hom).symm
  add_mem' := by
    intro first second hfirst hsecond sigma point
    change first _ + second _ = (M.obj.ρ sigma).hom (first point + second point)
    rw [hfirst, hsecond, map_add]
  neg_mem' := by
    intro section_ hsection sigma point
    change -section_ _ = (M.obj.ρ sigma).hom (-section_ point)
    rw [hsection, map_neg]

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of sections is precomposition with the map of separable point fibers. -/
def discreteSheafRestriction (M : DiscreteModuleCat ℤ (Gal(Ksep / K)))
    {U V : (Spec (.of K)).Etale} (morphism : U ⟶ V) :
    discreteSheafSections K Ksep M V →+ discreteSheafSections K Ksep M U where
  toFun section_ :=
    ⟨fun point : (etalePoint K Ksep).fiber.obj U ↦
      section_.val (((etalePoint K Ksep).fiber.map morphism).hom point), by
      intro sigma point
      have naturality :
          (etalePoint K Ksep).fiber.map morphism
              ((etaleFiberAction K Ksep sigma).app U point) =
            (etaleFiberAction K Ksep sigma).app V
              ((etalePoint K Ksep).fiber.map morphism point) :=
        (types_congr_hom
          ((etaleFiberAction K Ksep sigma).naturality morphism) point).symm
      exact (congrArg section_.val naturality).trans (section_.property sigma _)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A module morphism acts on sections by postcomposition. -/
def discreteSheafSectionsMap {M N : DiscreteModuleCat ℤ (Gal(Ksep / K))}
    (morphism : M ⟶ N) (U : (Spec (.of K)).Etale) :
    discreteSheafSections K Ksep M U →+ discreteSheafSections K Ksep N U where
  toFun section_ :=
    ⟨fun point ↦ morphism.hom.hom (section_.val point), by
      intro sigma point
      change morphism.hom.hom (section_.val
          ((etaleFiberAction K Ksep sigma).app U point)) = _
      rw [section_.property]
      exact ConcreteCategory.congr_hom (morphism.hom.comm sigma) (section_.val point)⟩
  map_zero' := by
    apply Subtype.ext
    funext point
    exact map_zero morphism.hom.hom.hom
  map_add' first second := by
    apply Subtype.ext
    funext point
    exact map_add morphism.hom.hom.hom (first.val point) (second.val point)

/-- The presheaf of equivariant functions on separable point fibers. -/
def discreteSheafPresheaf (M : DiscreteModuleCat ℤ (Gal(Ksep / K))) :
    (Spec (.of K)).Etaleᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (discreteSheafSections K Ksep M U.unop)
  map morphism := AddCommGrpCat.ofHom
    (discreteSheafRestriction K Ksep M morphism.unop)
  map_id U := by
    ext section_ point
    exact congrArg section_.val (types_congr_hom
      ((etalePoint K Ksep).fiber.map_id U.unop) point)
  map_comp first second := by
    ext section_ point
    exact congrArg section_.val (types_congr_hom
      ((etalePoint K Ksep).fiber.map_comp second.unop first.unop) point)

/-- Equivariant functions on point fibers satisfy étale descent. -/
theorem discreteSheafPresheaf_isSheaf (M : DiscreteModuleCat ℤ (Gal(Ksep / K))) :
    Presheaf.IsSheaf (Spec (.of K)).smallEtaleTopology
      (discreteSheafPresheaf K Ksep M) := sorry

/-- The étale sheaf associated to a discrete Galois module, with sections given by
equivariant functions on separable point fibers (Stacks, Tags 03QR and 03QT). -/
def discreteSheaf :
    DiscreteModuleCat ℤ (Gal(Ksep / K)) ⥤
      Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u} where
  obj M := ⟨discreteSheafPresheaf K Ksep M, discreteSheafPresheaf_isSheaf K Ksep M⟩
  map morphism := ObjectProperty.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom
        (discreteSheafSectionsMap K Ksep morphism U.unop)
      naturality := by
        intro U V restriction
        ext section_ point
        rfl }
  map_id M := by
    ext U section_ point
    rfl
  map_comp first second := by
    ext U section_ point
    rfl

/-- Restricting a section evaluates it at the postcomposed separable point. -/
theorem discreteSheaf_restrict_apply (M : DiscreteModuleCat ℤ (Gal(Ksep / K)))
    {U V : (Spec (.of K)).Etale} (morphism : U ⟶ V)
    (section_ : ((discreteSheaf K Ksep).obj M).obj.obj (op V))
    (point : (etalePoint K Ksep).fiber.obj U) :
    (((discreteSheaf K Ksep).obj M).obj.map morphism.op section_).val point =
      section_.val ((etalePoint K Ksep).fiber.map morphism point) := rfl

/-- On sections, the associated sheaf map is the given module map pointwise. -/
theorem discreteSheaf_map_apply {M N : DiscreteModuleCat ℤ (Gal(Ksep / K))}
    (morphism : M ⟶ N) (U : (Spec (.of K)).Etale)
    (section_ : ((discreteSheaf K Ksep).obj M).obj.obj (op U))
    (point : (etalePoint K Ksep).fiber.obj U) :
    ((((discreteSheaf K Ksep).map morphism).hom.app (op U)) section_).val point =
      morphism.hom.hom (section_.val point) := rfl

/-- The stalk of `discreteSheaf` is isomorphic to its input. -/
theorem discreteSheaf_spec (K Ksep : Type u) [Field K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep]
    (M : DiscreteModuleCat ℤ (Gal(Ksep / K))) :
    IsIsomorphic ((etaleStalkFunctor K Ksep).obj ((discreteSheaf K Ksep).obj M)) M := sorry

end GaloisCohomology

end
