/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Composition

/-!
# Composition of finite presentation morphisms of algebraic spaces

Morphisms of algebraic spaces of finite presentation are stable under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Finite presentation morphisms of algebraic spaces are stable under
composition. -/
instance finitePresentation_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@FinitePresentation S : MorphismProperty (AlgebraicSpace S)) where
  comp_mem f g hf hg :=
    { toLocallyOfFinitePresentation :=
        MorphismProperty.comp_mem (@LocallyOfFinitePresentation S) f g
          hf.toLocallyOfFinitePresentation hg.toLocallyOfFinitePresentation
      toQuasiCompact :=
        MorphismProperty.comp_mem (@QuasiCompact S) f g hf.toQuasiCompact hg.toQuasiCompact
      toQuasiSeparated :=
        MorphismProperty.comp_mem (@QuasiSeparated S) f g hf.toQuasiSeparated hg.toQuasiSeparated }

/-- The composition of finite presentation morphisms of algebraic spaces is of
finite presentation. -/
instance finitePresentation_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [FinitePresentation f] [FinitePresentation g] :
    FinitePresentation (f ≫ g) :=
  MorphismProperty.comp_mem (@FinitePresentation S) f g inferInstance inferInstance

end AlgebraicGeometry.AlgebraicSpace
