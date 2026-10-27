/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.RingedTopos
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale.SmallSections

/-!
# Small fppf direct-image sections for algebraic stacks

Restriction to the étale topology gives small compatible sections of fppf
sheaves along morphisms of algebraic stacks.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Morphisms between algebraic stacks have small fppf sheaf sections, by
restricting the same presheaf to the étale topology and using its atlas certificate. -/
instance hasSmallAssociatedFppfTypeSections_of_algebraicStack {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    HasSmallAssociatedTypeSections f StandardTopology.fppf where
  small F Z := AlgebraicStack.EtaleSmallSections.sectionsSmall f
    ⟨F.obj, Presheaf.IsSheaf.of_le (etaleTopology_le_fppfTopology X) F.property⟩ Z.unop

end AlgebraicGeometry.GroupoidsOver
