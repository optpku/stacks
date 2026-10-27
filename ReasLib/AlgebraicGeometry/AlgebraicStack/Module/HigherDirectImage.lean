/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.HigherDirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact

/-!
# Local quasi-coherence of étale higher direct images
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- Étale higher direct images of locally quasi-coherent modules along a
quasi-compact and quasi-separated morphism of algebraic stacks are locally
quasi-coherent. Resolutions are computed after the explicit coefficient lift. -/
@[stacks 075Z]
instance isLocallyQuasiCoherent_higherDirectImage
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (F : GroupoidsOver.etaleModules X) [IsLocallyQuasiCoherent F] (i : ℕ) :
    IsLocallyQuasiCoherentLift (GroupoidsOver.moduleHigherDirectImage f F i) :=
  sorry

/-- An explicit local-quasi-coherence hypothesis yields local quasi-coherence
of every étale higher direct image along a quasi-compact quasi-separated
morphism of algebraic stacks. -/
theorem isLocallyQuasiCoherent_higherDirectImage_of
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {F : GroupoidsOver.etaleModules X} (hF : IsLocallyQuasiCoherent F) (i : ℕ) :
    IsLocallyQuasiCoherentLift (GroupoidsOver.moduleHigherDirectImage f F i) :=
  isLocallyQuasiCoherent_higherDirectImage f F i

/-- Étale higher direct image along a quasi-compact quasi-separated morphism
of algebraic stacks maps the property of local quasi-coherence into itself. -/
theorem mapsHigherDirectImage_locallyQuasiCoherent
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (i : ℕ) :
    locallyQuasiCoherent X ≤
      ObjectProperty.inverseImage (fun G ↦ IsLocallyQuasiCoherentLift G)
        (GroupoidsOver.moduleHigherDirectImageFunctor f i) := by
  intro F hF
  exact isLocallyQuasiCoherent_higherDirectImage_of f hF i

end AlgebraicGeometry.AlgebraicStack
