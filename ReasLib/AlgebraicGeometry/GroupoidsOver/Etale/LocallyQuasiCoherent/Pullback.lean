/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.LocallyQuasiCoherent

/-!
# Inverse image of locally quasi-coherent étale modules

Inverse image along a morphism of categories fibred in groupoids preserves
quasi-coherence after restriction to every small étale site.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}

/-- Inverse image along a morphism of categories fibred in groupoids preserves
locally quasi-coherent étale modules. -/
instance moduleInverseImage_isLocallyQuasiCoherent (f : X ⟶ Y)
    (G : etaleModules Y) [IsLocallyQuasiCoherent G] :
    IsLocallyQuasiCoherent ((etaleModuleInverseImage f).obj G) := sorry

end AlgebraicGeometry.GroupoidsOver
