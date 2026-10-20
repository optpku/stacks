/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import ReasLib.Topology.Sheaf.Support

/-!
# Supports of sheaves of modules

This module specializes topological sheaf support to sheaves of modules over an arbitrary sheaf
of rings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules

variable {X : TopCat.{u}} {𝒪 : X.Sheaf RingCat.{u}}

/-- Support of a local section of a sheaf of modules: the support of the same section in the
underlying additive sheaf. -/
@[stacks 01AU "local module-section support"]
abbrev localSectionSupport {U : Opens X} {ℱ : SheafOfModules 𝒪}
    (s : ℱ.val.obj (op U)) : Set U :=
  abelianSheafSectionSupport ((toSheaf 𝒪).obj ℱ) s

/-- Membership in the support of a local module section is nonvanishing of its germ. -/
@[simp]
theorem mem_localSectionSupport_iff {U : Opens X} {ℱ : SheafOfModules 𝒪}
    (s : ℱ.val.obj (op U)) (x : U) :
    x ∈ localSectionSupport s ↔
      TopCat.Presheaf.germ ℱ.val.presheaf U x.1 x.2 s ≠ 0 := sorry

/-- The support of a local module section is closed in its domain. -/
@[stacks 01AU "(1)"]
theorem isClosed_localSectionSupport
    {U : Opens X} {M : SheafOfModules 𝒪} (s : M.val.obj (op U)) :
    IsClosed (localSectionSupport s) := sorry

/-- The support of a scalar multiple lies in the intersection of the supports of the scalar and
the module section. -/
@[stacks 01AU "(2)"]
theorem localSectionSupport_smul_subset
    {U : Opens X} {M : SheafOfModules 𝒪}
    (f : 𝒪.presheaf.obj (op U)) (s : M.val.obj (op U)) :
    localSectionSupport (f • s) ⊆
      TopCat.Sheaf.ringSectionSupport f ∩ localSectionSupport s := sorry

/-- The support of a sum of local module sections lies in the union of their supports. -/
@[stacks 01AU "(3)"]
theorem localSectionSupport_add_subset
    {U : Opens X} {M : SheafOfModules 𝒪} (s t : M.val.obj (op U)) :
    localSectionSupport (s + t) ⊆
      localSectionSupport s ∪ localSectionSupport t := sorry

/-- A morphism of module sheaves cannot enlarge the support of a local section. -/
@[stacks 01AU "(5)"]
theorem localSectionSupport_map_subset
    {U : Opens X} {M N : SheafOfModules 𝒪} (φ : M ⟶ N)
    (s : M.val.obj (op U)) :
    localSectionSupport (φ.val.app (op U) s) ⊆ localSectionSupport s := sorry

/-- Support of a sheaf of modules: the support of its underlying additive sheaf. -/
@[stacks 01AT "module support"]
abbrev support (ℱ : SheafOfModules 𝒪) : Set X :=
  abelianSheafSupport ((toSheaf 𝒪).obj ℱ)

/-- The object property of module sheaves supported on a prescribed subset. -/
@[stacks 01AT "module support property"]
abbrev supportedOn (T : Set X) : ObjectProperty (SheafOfModules 𝒪) :=
  fun M ↦ support M ⊆ T

/-- Support containment is closed under isomorphisms of module sheaves. -/
instance supportedOn_isClosedUnderIsomorphisms (T : Set X) :
    ObjectProperty.IsClosedUnderIsomorphisms (supportedOn (𝒪 := 𝒪) T) := sorry

namespace supportedOn

/-- Transport support containment across a module-sheaf isomorphism. -/
theorem of_iso {M N : SheafOfModules 𝒪} (e : M ≅ N) (T : Set X)
    (hM : supportedOn T M) : supportedOn T N := sorry

/-- Support containment is equivalent on isomorphic module sheaves. -/
theorem iff_of_iso {M N : SheafOfModules 𝒪} (e : M ≅ N) (T : Set X) :
    supportedOn T M ↔ supportedOn T N := sorry

end supportedOn

/-- Membership in `supportedOn` is exactly the corresponding support inclusion. -/
@[simp]
theorem mem_supportedOn_iff (T : Set X) (M : SheafOfModules 𝒪) :
    supportedOn T M ↔ support M ⊆ T := Iff.rfl

/-- Membership in a module sheaf's support is nontriviality of its additive stalk. -/
@[simp]
theorem mem_support_iff (M : SheafOfModules 𝒪) (x : X) :
    x ∈ support M ↔
      ¬ IsZero (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf x) := sorry

/-- The support of a module sheaf is the union of the ambient images of the supports of all local
sections. -/
@[stacks 01AU "(4)"]
theorem support_eq_iUnion_localSectionSupport
    (M : SheafOfModules 𝒪) :
    support M =
      ⋃ (U : Opens X) (s : M.val.obj (op U)),
        Subtype.val '' localSectionSupport s := sorry

/-- Support of a global module section: the points where its germ is nonzero. -/
@[stacks 01AT "global section support"]
abbrev sectionSupport {M : SheafOfModules 𝒪} (s : M.sections) : Set X :=
  abelianSheafGlobalSectionSupport
    ((toSheaf 𝒪).obj M : X.Sheaf AddCommGrpCat.{u}) (s.val (op (⊤ : Opens X)))

/-- Membership in the support of a global module section is nonvanishing of its germ. -/
@[simp]
theorem mem_sectionSupport_iff {M : SheafOfModules 𝒪} (s : M.sections) (x : X) :
    x ∈ sectionSupport s ↔
      TopCat.Presheaf.Γgerm M.val.presheaf x (s.val (op ⊤)) ≠ 0 := sorry

/-- The ambient support of a global section is the image of its local support over the top open. -/
theorem sectionSupport_eq_image_localSectionSupport
    {M : SheafOfModules 𝒪} (s : M.sections) :
    sectionSupport s =
      Subtype.val '' localSectionSupport (s.val (op (⊤ : Opens X))) := sorry

/-- If the support of a global module section misses an open set, its restriction to that open
set is zero. -/
theorem eval_eq_zero_of_disjoint_sectionSupport
    {M : SheafOfModules 𝒪} (s : M.sections) (U : Opens X)
    (h : Disjoint (sectionSupport s) (U : Set X)) :
    s.val (op U) = 0 := sorry

end SheafOfModules
