/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cohomology of Derived Truncations

This leaf gives the degree-range forms of the standard cohomology invariance
of lower and upper truncations. It also packages the canonical homology maps
as natural transformations, without choosing inverses for their components.
-/

open CategoryTheory
open DerivedCategory.TStructure

universe w v u

namespace CategoryTheory

namespace DerivedCategory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

namespace TruncGE

/-- Stacks 08J5 and 0H72: the canonical map from an object to its lower truncation at
degree `a` induces an isomorphism on cohomology in every degree `i ≥ a`. -/
@[stacks 08J5, stacks 0H72]
theorem homologyMap_isIso
    (K : DerivedCategory 𝒜) (a i : ℤ) (h : a ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor 𝒜 i).map ((t.truncGEπ a).app K)) := sorry

/-- In the stable degree range, lower truncation has canonically isomorphic homology to the
original derived object. -/
@[stacks 08J5, stacks 0H72]
noncomputable def homologyIso
    (K : DerivedCategory 𝒜) (a i : ℤ) (h : a ≤ i) :
    (DerivedCategory.homologyFunctor 𝒜 i).obj ((t.truncGE a).obj K) ≅
      (DerivedCategory.homologyFunctor 𝒜 i).obj K :=
  letI : IsIso ((DerivedCategory.homologyFunctor 𝒜 i).map ((t.truncGEπ a).app K)) :=
    homologyMap_isIso K a i h
  (asIso ((DerivedCategory.homologyFunctor 𝒜 i).map ((t.truncGEπ a).app K))).symm

/-- The inverse of `homologyIso` is the homology map induced by the lower-truncation
projection. -/
@[simp, stacks 08J5, stacks 0H72]
theorem homologyIso_inv
    (K : DerivedCategory 𝒜) (a i : ℤ) (h : a ≤ i) :
    (homologyIso K a i h).inv =
      (DerivedCategory.homologyFunctor 𝒜 i).map ((t.truncGEπ a).app K) := sorry

/-- Naturality of the homology maps induced by the canonical lower-truncation
projections, in the forward direction used by natural transformations. -/
@[reassoc, stacks 08J5, stacks 0H72]
theorem homologyNatTrans_naturality
    (a i : ℤ) {K L : DerivedCategory 𝒜} (f : K ⟶ L) :
    (DerivedCategory.homologyFunctor 𝒜 i).map f ≫
        (DerivedCategory.homologyFunctor 𝒜 i).map ((t.truncGEπ a).app L) =
      (DerivedCategory.homologyFunctor 𝒜 i).map ((t.truncGEπ a).app K) ≫
        (DerivedCategory.homologyFunctor 𝒜 i).map ((t.truncGE a).map f) := sorry

variable (𝒜) in
/-- Stacks 08J5 and 0H72: the canonical lower-truncation projections induce
a natural transformation on homology in every degree. -/
@[stacks 08J5, stacks 0H72]
noncomputable def homologyNatTrans (a i : ℤ) :
    DerivedCategory.homologyFunctor 𝒜 i ⟶
      t.truncGE a ⋙ DerivedCategory.homologyFunctor 𝒜 i where
  app K :=
    (DerivedCategory.homologyFunctor 𝒜 i).map ((t.truncGEπ a).app K)
  naturality _ _ f := homologyNatTrans_naturality a i f

/-- A component of the lower-truncation homology transformation is the map
induced by the canonical truncation projection. -/
@[simp, stacks 08J5, stacks 0H72]
theorem homologyNatTrans_app (a i : ℤ) (K : DerivedCategory 𝒜) :
    (homologyNatTrans 𝒜 a i).app K =
      (DerivedCategory.homologyFunctor 𝒜 i).map ((t.truncGEπ a).app K) := sorry

/-- Every component of the lower-truncation homology transformation is an
isomorphism. -/
@[stacks 08J5, stacks 0H72]
theorem homologyNatTrans_app_isIso (a i : ℤ) (h : a ≤ i)
    (K : DerivedCategory 𝒜) :
    IsIso ((homologyNatTrans 𝒜 a i).app K) := sorry

variable (𝒜) in
/-- In the stable degree range, the lower-truncation homology transformation
is an isomorphism of functors. -/
@[stacks 08J5, stacks 0H72]
theorem homologyNatTrans_isIso (a i : ℤ) (h : a ≤ i) :
    IsIso (homologyNatTrans 𝒜 a i) := sorry

end TruncGE

namespace TruncLT

/-- Stacks 08J5: the canonical map from an upper truncation at degree `b`
to the original object induces an isomorphism on homology in every degree
`i < b`. -/
@[stacks 08J5]
theorem homologyMap_isIso
    (K : DerivedCategory 𝒜) (b i : ℤ) (h : i < b) :
    IsIso ((DerivedCategory.homologyFunctor 𝒜 i).map ((t.truncLTι b).app K)) := sorry

/-- Naturality of the homology maps induced by the canonical upper-truncation
inclusions, in the forward direction used by natural transformations. -/
@[reassoc, stacks 08J5]
theorem homologyNatTrans_naturality
    (b i : ℤ) {K L : DerivedCategory 𝒜} (f : K ⟶ L) :
    (DerivedCategory.homologyFunctor 𝒜 i).map ((t.truncLT b).map f) ≫
        (DerivedCategory.homologyFunctor 𝒜 i).map ((t.truncLTι b).app L) =
      (DerivedCategory.homologyFunctor 𝒜 i).map ((t.truncLTι b).app K) ≫
        (DerivedCategory.homologyFunctor 𝒜 i).map f := sorry

variable (𝒜) in
/-- Stacks 08J5: the canonical upper-truncation inclusions induce a natural
transformation on homology in every degree. -/
@[stacks 08J5]
noncomputable def homologyNatTrans (b i : ℤ) :
    t.truncLT b ⋙ DerivedCategory.homologyFunctor 𝒜 i ⟶
      DerivedCategory.homologyFunctor 𝒜 i where
  app K :=
    (DerivedCategory.homologyFunctor 𝒜 i).map ((t.truncLTι b).app K)
  naturality _ _ f := homologyNatTrans_naturality b i f

/-- A component of the upper-truncation homology transformation is the map
induced by the canonical truncation inclusion. -/
@[simp, stacks 08J5]
theorem homologyNatTrans_app (b i : ℤ) (K : DerivedCategory 𝒜) :
    (homologyNatTrans 𝒜 b i).app K =
      (DerivedCategory.homologyFunctor 𝒜 i).map ((t.truncLTι b).app K) := sorry

/-- Every component of the upper-truncation homology transformation is an
isomorphism. -/
@[stacks 08J5]
theorem homologyNatTrans_app_isIso (b i : ℤ) (h : i < b)
    (K : DerivedCategory 𝒜) :
    IsIso ((homologyNatTrans 𝒜 b i).app K) := sorry

variable (𝒜) in
/-- In the stable degree range, the upper-truncation homology transformation
is an isomorphism of functors. -/
@[stacks 08J5]
theorem homologyNatTrans_isIso (b i : ℤ) (h : i < b) :
    IsIso (homologyNatTrans 𝒜 b i) := sorry

end TruncLT

section Compatibility

/-! These declarations preserve the pre-neutralization names used by older chapter files.
The names are intentionally kept as bridges only; new code should use the namespaced
`TruncGE.homologyMap_isIso` and `TruncLT.homologyMap_isIso` owners above. -/

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- Compatibility bridge for the equal-degree lower-truncation homology test.
Prefer `DerivedCategory.TruncGE.homologyMap_isIso` with `a = i`. -/
@[stacks 08J5]
theorem isIso_homologyMap_truncGEπ
    (K : DerivedCategory A) (i : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor A i).map
      ((t.truncGEπ i).app K)) := sorry

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- Compatibility bridge for the degree-range lower-truncation homology test.
Prefer `DerivedCategory.TruncGE.homologyMap_isIso`. -/
@[stacks 08J5]
theorem isIso_homologyMap_truncGEπ_of_le
    (K : DerivedCategory 𝒜) (a i : ℤ) (h : a ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor 𝒜 i).map
      ((t.truncGEπ a).app K)) := sorry

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- Compatibility bridge for successor upper-truncation homology.
Prefer `DerivedCategory.TruncLT.homologyMap_isIso` with the inequality
`n₀ < n₁`. -/
@[stacks 08J5]
theorem isIso_homologyMap_truncLTι
    (K : DerivedCategory A) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    IsIso ((DerivedCategory.homologyFunctor A n₀).map
      ((t.truncLTι n₁).app K)) := sorry

end Compatibility

end DerivedCategory

end CategoryTheory
