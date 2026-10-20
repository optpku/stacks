/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigEtale

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.RigEtale

/-- If a composite of morphisms of locally Noetherian formal algebraic spaces
and its second factor are rig-étale, then its first factor is rig-étale. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [RigEtale (f ≫ g)] [RigEtale g] : RigEtale f :=
  sorry

/-- If a composite of morphisms of locally Noetherian formal algebraic spaces
is rig-étale and its second factor is an adic monomorphism, then its first
factor is rig-étale. Adicness means representability by algebraic spaces. -/
theorem of_comp_adic_mono {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [RigEtale (f ≫ g)]
    (hg : AlgebraicSpace.representableByAlgebraicSpaces g) [Mono g] :
    RigEtale f :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.RigEtale
