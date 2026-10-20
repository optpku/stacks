/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap103.Definition_103_7_1_FlatBaseChange
public import stacks_project.Chap103.Lemma_103_6_2

/-!
# Flat base change of étale higher direct images

Along a quasi-compact and quasi-separated morphism of algebraic stacks, étale
higher direct images of locally quasi-coherent modules with the flat base
change property again have the flat base change property.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- Lemma 103.7.3: if `f : X ⟶ Y` is a quasi-compact and quasi-separated morphism
of algebraic stacks and `F` is a locally quasi-coherent étale `𝒪_X`-module
with the flat base change property, then the étale higher direct image
`R^i f_* F`, computed in the étale topology on `GroupoidsOver.etaleModules`,
has the flat base change property. -/
@[stacks 0765]
instance hasFlatBaseChange_higherDirectImage
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (F : GroupoidsOver.etaleModules X) [IsLocallyQuasiCoherent F]
    [HasFlatBaseChange F] (i : ℕ) :
    HasFlatBaseChange (GroupoidsOver.moduleHigherDirectImage f F i) :=
  sorry

/-- Explicit-hypothesis form of étale higher direct images preserving the
flat base change property along a quasi-compact quasi-separated morphism of
algebraic stacks. -/
theorem hasFlatBaseChange_higherDirectImage_of
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {F : GroupoidsOver.etaleModules X} (h_lqc : IsLocallyQuasiCoherent F)
    (h_fbc : HasFlatBaseChange F) (i : ℕ) :
    HasFlatBaseChange (GroupoidsOver.moduleHigherDirectImage f F i) :=
  sorry

/-- Object-property form: étale `R^i f_*` sends locally quasi-coherent modules
with the flat base change property on `X` to modules with the flat base
change property on `Y`. -/
theorem mapsHigherDirectImage_hasFlatBaseChange
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (i : ℕ) :
    locallyQuasiCoherent X ⊓ hasFlatBaseChange X ≤
      (hasFlatBaseChange Y).inverseImage
        (GroupoidsOver.moduleHigherDirectImageFunctor f i) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
