/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Sheaves.Stalks
public import ReasLib.Topology.Sheaves.Ring.Definition

/-!
# Supports of additive and ring sheaves

This module owns the support constructions that use only a topological space and a sheaf of
additive groups or rings. Module-sheaf and ringed-space specializations live in their respective
algebraic support modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

noncomputable section

universe u

section AbelianSheaf

variable {X : TopCat.{u}} {U : Opens X}

/-- The support of a local section of an abelian sheaf: points where the germ is nonzero. -/
@[stacks 01AU "local-section support, additive core"]
def abelianSheafSectionSupport (ℱ : X.Sheaf AddCommGrpCat.{u}) (s : ℱ.presheaf.obj (op U)) :
    Set U :=
  { x | ℱ.presheaf.germ U x.1 x.2 s ≠ 0 }

/-- Membership in a local section's support is nonvanishing of its germ. -/
@[simp]
theorem mem_abelianSheafSectionSupport_iff
    (ℱ : X.Sheaf AddCommGrpCat.{u}) (s : ℱ.presheaf.obj (op U)) (x : U) :
    x ∈ abelianSheafSectionSupport ℱ s ↔ ℱ.presheaf.germ U x.1 x.2 s ≠ 0 := sorry

/-- The support of a local section of an additive sheaf is closed in its domain. -/
@[stacks 01AU "(1), additive core"]
theorem isClosed_abelianSheafSectionSupport
    (ℱ : X.Sheaf AddCommGrpCat.{u}) (s : ℱ.presheaf.obj (op U)) :
    IsClosed (abelianSheafSectionSupport ℱ s) := sorry

/-- The support of a sum of local sections lies in the union of their supports. -/
@[stacks 01AU "(3), additive core"]
theorem abelianSheafSectionSupport_add_subset
    (ℱ : X.Sheaf AddCommGrpCat.{u}) (s t : ℱ.presheaf.obj (op U)) :
    abelianSheafSectionSupport ℱ (s + t) ⊆
      abelianSheafSectionSupport ℱ s ∪ abelianSheafSectionSupport ℱ t := sorry

/-- A morphism of additive sheaves cannot enlarge the support of a local section. -/
@[stacks 01AU "(5), additive core"]
theorem abelianSheafSectionSupport_map_subset
    {ℱ 𝒢 : X.Sheaf AddCommGrpCat.{u}} (φ : ℱ ⟶ 𝒢)
    (s : ℱ.presheaf.obj (op U)) :
    abelianSheafSectionSupport 𝒢 (φ.hom.app (op U) s) ⊆
      abelianSheafSectionSupport ℱ s := sorry

/-- The ambient support of a global section of an abelian sheaf: the points where its germ is
nonzero. -/
@[stacks 01AT "additive global-section support"]
def abelianSheafGlobalSectionSupport
    (ℱ : X.Sheaf AddCommGrpCat.{u}) (s : ℱ.presheaf.obj (op (⊤ : Opens X))) : Set X :=
  {x | ℱ.presheaf.Γgerm x s ≠ 0}

/-- Membership in the ambient support of a global section is nonvanishing of its germ. -/
@[simp]
theorem mem_abelianSheafGlobalSectionSupport_iff
    (ℱ : X.Sheaf AddCommGrpCat.{u}) (s : ℱ.presheaf.obj (op (⊤ : Opens X))) (x : X) :
    x ∈ abelianSheafGlobalSectionSupport ℱ s ↔ ℱ.presheaf.Γgerm x s ≠ 0 := sorry

/-- A global section restricts to zero on every open disjoint from its ambient support. -/
theorem restrict_eq_zero_of_disjoint_abelianSheafGlobalSectionSupport
    (ℱ : X.Sheaf AddCommGrpCat.{u}) (s : ℱ.presheaf.obj (op (⊤ : Opens X)))
    (U : Opens X) (h : Disjoint (abelianSheafGlobalSectionSupport ℱ s) (U : Set X)) :
    ℱ.presheaf.map (homOfLE (le_top : U ≤ (⊤ : Opens X))).op s = 0 := sorry

/-- The support of an abelian sheaf: points where the stalk is nonzero. -/
@[stacks 01AT "additive core"]
def abelianSheafSupport (ℱ : X.Sheaf AddCommGrpCat.{u}) : Set X :=
  { x | ¬ IsZero (ℱ.presheaf.stalk x) }

/-- Membership in an abelian sheaf's support is nontriviality of its stalk. -/
@[simp]
theorem mem_abelianSheafSupport_iff (ℱ : X.Sheaf AddCommGrpCat.{u}) (x : X) :
    x ∈ abelianSheafSupport ℱ ↔ ¬ IsZero (ℱ.presheaf.stalk x) := sorry

/-- The support of an additive sheaf is the union of the ambient images of the supports of all
local sections. -/
@[stacks 01AU "(4), additive core"]
theorem abelianSheafSupport_eq_iUnion_sectionSupport
    (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    abelianSheafSupport ℱ =
      ⋃ (U : Opens X) (s : ℱ.presheaf.obj (op U)),
        Subtype.val '' abelianSheafSectionSupport ℱ s := sorry

end AbelianSheaf

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-- Support of a local section of a sheaf of rings, computed in the underlying additive sheaf. -/
@[stacks 01AU "(2), ring-sheaf section support"]
abbrev ringSectionSupport {U : Opens X} {ℱ : X.Sheaf RingCat.{u}}
    (s : ℱ.presheaf.obj (op U)) : Set U :=
  abelianSheafSectionSupport
    ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ RingCat AddCommGrpCat)).obj ℱ) s

/-- Membership in the support of a local ring section is nonvanishing of its germ. -/
@[simp]
theorem mem_ringSectionSupport_iff
    {U : Opens X} {ℱ : X.Sheaf RingCat.{u}}
    (s : ℱ.presheaf.obj (op U)) (x : U) :
    x ∈ ringSectionSupport s ↔ ℱ.presheaf.germ U x.1 x.2 s ≠ 0 := sorry

/-- Support of a sheaf of rings: the support of its underlying additive sheaf. -/
abbrev ringSheafSupport (ℱ : X.Sheaf RingCat.{u}) : Set X :=
  abelianSheafSupport
    ((sheafCompose (Opens.grothendieckTopology X) (forget₂ RingCat AddCommGrpCat)).obj ℱ)

/-- A point belongs to the support of a ring sheaf exactly when the germ of its global unit is
nonzero. -/
@[stacks 01AV "ring-sheaf support membership"]
theorem mem_ringSheafSupport_iff_one_germ_ne_zero
    (ℱ : X.Sheaf RingCat.{u}) (x : X) :
    x ∈ ringSheafSupport ℱ ↔
      ℱ.presheaf.Γgerm x (1 : ℱ.presheaf.obj (op ⊤)) ≠ 0 := sorry

/-- The support of a sheaf of rings on a topological space is closed. -/
@[stacks 01AV]
theorem isClosed_ringSheafSupport
    (ℱ : X.Sheaf RingCat.{u}) :
    IsClosed (ringSheafSupport ℱ) := sorry

end TopCat.Sheaf
