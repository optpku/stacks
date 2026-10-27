/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.HigherDirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre

/-!
# Étale-module rules on algebraic stacks

Weak Serre rules on enlarged-coefficient étale modules are stable under smooth
inverse image, detected on smooth coverings, and preserved by affine higher
direct images.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- A rule associating to every algebraic stack a subcategory of étale
`𝒪`-modules, subject to weak Serre, smooth inverse-image, covering-detection,
and affine higher-direct-image axioms. -/
structure EtaleModuleRule (S : Scheme.{u}) where
  /-- The subcategory of étale `𝒪_X`-modules attached to each algebraic stack. -/
  predicate (X : GroupoidsOver S) [AlgebraicStack X] :
    ObjectProperty (EtaleModulesLift X)
  /-- Each assigned subcategory is a weak Serre class. -/
  isWeakSerre (X : GroupoidsOver S) [AlgebraicStack X] :
    (predicate X).IsWeakSerreClass
  /-- Inverse image along a smooth morphism of algebraic stacks preserves the
  rule. -/
  mapsInverseImage_of_smooth {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Smooth f] :
    predicate Y ≤ (predicate X).inverseImage (etaleModuleInverseImageLift f)
  /-- Membership in the rule is detected on a jointly point-covering family of
  smooth morphisms of algebraic stacks. -/
  mem_iff_of_smoothCovering {X : GroupoidsOver S} [AlgebraicStack X]
      {ι : Type (u + 1)} {Xi : ι → GroupoidsOver S} [∀ i, AlgebraicStack (Xi i)]
      (f : ∀ i, Xi i ⟶ X) [∀ i, Smooth (f i)]
      (h_cover : ∀ x : Points X, ∃ i, x ∈ Set.range (Points.map (f i)))
      (F : EtaleModulesLift X) :
    predicate X F ↔ ∀ i, predicate (Xi i) ((etaleModuleInverseImageLift (f i)).obj F)
  /-- Higher direct images in the étale topology preserve the rule when source
  and target are representable by affine schemes. -/
  mapsHigherDirectImage_of_affine {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
      (hX : IsRepresentableByAffine X) (hY : IsRepresentableByAffine Y)
      (i : ℕ) {F : EtaleModulesLift X} (hF : predicate X F) :
    predicate Y ((etaleHigherDirectImageLiftFunctor f i).obj F)

namespace EtaleModuleRule

/-- The maximal étale-module rule, sending every algebraic stack to the full
category of étale modules. -/
def max (S : Scheme.{u}) : EtaleModuleRule S where
  predicate _ := ⊤
  isWeakSerre X :=
    { exists_prop := ⟨0, trivial⟩
      prop_X₂_of_exact₄ := by intros; trivial }
  mapsInverseImage_of_smooth := by intros; trivial
  mem_iff_of_smoothCovering := by intros; exact ⟨fun _ _ ↦ trivial, fun _ ↦ trivial⟩
  mapsHigherDirectImage_of_affine := by intros; trivial

variable {S : Scheme.{u}} (M : EtaleModuleRule S)

/-- Inverse image along a smooth morphism sends objects of the rule on the
target into the rule on the source. -/
theorem mapsInverseImage_obj {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Smooth f]
    {F : EtaleModulesLift Y} (hF : M.predicate Y F) :
    M.predicate X ((etaleModuleInverseImageLift f).obj F) :=
  M.mapsInverseImage_of_smooth f F hF

/-- Higher direct images in the étale topology send objects of the rule into
the rule, when source and target are representable by affine schemes. -/
theorem mapsHigherDirectImage_of_affine_obj {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (hX : IsRepresentableByAffine X) (hY : IsRepresentableByAffine Y)
    (i : ℕ) {F : EtaleModulesLift X} (hF : M.predicate X F) :
    M.predicate Y ((etaleHigherDirectImageLiftFunctor f i).obj F) :=
  M.mapsHigherDirectImage_of_affine f hX hY i hF

end EtaleModuleRule

/-- Étale higher direct images along a quasi-compact quasi-separated morphism
preserve every weak Serre rule stable under smooth inverse image, detected on
smooth point-covering families, and preserved by affine higher direct images. -/
@[stacks 076Z]
theorem mapsHigherDirectImage {S : Scheme.{u}} (M : EtaleModuleRule S)
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (i : ℕ) :
    M.predicate X ≤ (M.predicate Y).inverseImage (etaleHigherDirectImageLiftFunctor f i) :=
  sorry

/-- Membership form of étale higher-direct-image stability along a
quasi-compact quasi-separated morphism of algebraic stacks. -/
theorem mem_higherDirectImage {S : Scheme.{u}} (M : EtaleModuleRule S)
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (i : ℕ)
    {F : EtaleModulesLift X} (hF : M.predicate X F) :
    M.predicate Y ((etaleHigherDirectImageLiftFunctor f i).obj F) :=
  mapsHigherDirectImage M f i F hF

end AlgebraicGeometry.AlgebraicStack
