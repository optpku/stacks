/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Fppf.SmallSections
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Modules
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre

/-!
# Fppf-module rules on algebraic stacks

Weak Serre rules on fppf modules are stable under smooth inverse image,
detected on smooth coverings, and preserved by affine higher direct images.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- A rule associating to every algebraic stack a subcategory of fppf
`𝒪`-modules, subject to weak Serre, smooth inverse-image, covering-detection,
and affine higher-direct-image axioms. -/
structure FppfModuleRule (S : Scheme.{u}) where
  /-- The subcategory of fppf `𝒪_X`-modules attached to each algebraic stack. -/
  predicate (X : GroupoidsOver S) [AlgebraicStack X] :
    ObjectProperty (fppfModules X)
  /-- Each assigned subcategory is a weak Serre class. -/
  isWeakSerre (X : GroupoidsOver S) [AlgebraicStack X] :
    (predicate X).IsWeakSerreClass
  /-- Inverse image along a smooth morphism of algebraic stacks preserves the
  rule. -/
  mapsInverseImage_of_smooth {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Smooth f] :
    predicate Y ≤ (predicate X).inverseImage (fppfModuleInverseImage f)
  /-- Membership in the rule is detected on a jointly point-covering family of
  smooth morphisms of algebraic stacks. -/
  mem_iff_of_smoothCovering {X : GroupoidsOver S} [AlgebraicStack X]
      {ι : Type (u + 1)} {Xi : ι → GroupoidsOver S} [∀ i, AlgebraicStack (Xi i)]
      (f : ∀ i, Xi i ⟶ X) [∀ i, Smooth (f i)]
      (h_cover : ∀ x : Points X, ∃ i, x ∈ Set.range (Points.map (f i)))
      (F : fppfModules X) :
    predicate X F ↔ ∀ i, predicate (Xi i) ((fppfModuleInverseImage (f i)).obj F)
  /-- Higher direct images in the fppf topology preserve the rule when source
  and target are representable by affine schemes. -/
  mapsHigherDirectImage_of_affine {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
      (hX : IsRepresentableByAffine X) (hY : IsRepresentableByAffine Y)
      (i : ℕ) {F : fppfModules X} (hF : predicate X F) :
    predicate Y ((fppfHigherDirectImageFunctor f i).obj F)

namespace FppfModuleRule

/-- The maximal fppf-module rule, sending every algebraic stack to the full
category of fppf modules. -/
def max (S : Scheme.{u}) : FppfModuleRule S where
  predicate _ := ⊤
  isWeakSerre X := inferInstance
  mapsInverseImage_of_smooth := by intros; trivial
  mem_iff_of_smoothCovering := by
    intros
    constructor <;> intros <;> trivial
  mapsHigherDirectImage_of_affine := by intros; trivial

variable {S : Scheme.{u}} (M : FppfModuleRule S)

/-- Inverse image along a smooth morphism sends objects of the rule on the
target into the rule on the source. -/
theorem mapsInverseImage_obj {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Smooth f]
    {F : fppfModules Y} (hF : M.predicate Y F) :
    M.predicate X ((fppfModuleInverseImage f).obj F) :=
  M.mapsInverseImage_of_smooth f F hF

/-- Higher direct images in the fppf topology send objects of the rule into
the rule, when source and target are representable by affine schemes. -/
theorem mapsHigherDirectImage_of_affine_obj {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (hX : IsRepresentableByAffine X) (hY : IsRepresentableByAffine Y)
    (i : ℕ) {F : fppfModules X} (hF : M.predicate X F) :
    M.predicate Y ((fppfHigherDirectImageFunctor f i).obj F) :=
  M.mapsHigherDirectImage_of_affine f hX hY i hF

/-- Fppf higher direct images along a quasi-compact quasi-separated morphism
preserve every weak Serre rule stable under smooth inverse image, detected on
smooth point-covering families, and preserved by affine higher direct images. -/
@[stacks 0770]
theorem mapsHigherDirectImage {S : Scheme.{u}} (M : FppfModuleRule S)
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (i : ℕ) :
    M.predicate X ≤ (M.predicate Y).inverseImage (fppfHigherDirectImageFunctor f i) :=
  sorry

/-- Membership in a rule is preserved by fppf higher direct image along a
quasi-compact quasi-separated morphism of algebraic stacks. -/
theorem mem_higherDirectImage {S : Scheme.{u}} (M : FppfModuleRule S)
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (i : ℕ)
    {F : fppfModules X} (hF : M.predicate X F) :
    M.predicate Y ((fppfHigherDirectImageFunctor f i).obj F) :=
  mapsHigherDirectImage M f i F hF

end FppfModuleRule

end AlgebraicGeometry.AlgebraicStack
