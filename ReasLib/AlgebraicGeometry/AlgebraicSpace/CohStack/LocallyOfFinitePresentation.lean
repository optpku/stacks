/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.StructureMorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Local finite presentation of the coherent-sheaf structure morphism
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- For a separated morphism `f : X ⟶ B` of finite presentation, the canonical
structure morphism of the stack of coherent sheaves over `B` is locally of
finite presentation. -/
instance instLocallyOfFinitePresentation_forget (f : X ⟶ B)
    [FinitePresentation f] [Separated f] :
    Hom.LocallyOfFinitePresentation (forget f) := sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
