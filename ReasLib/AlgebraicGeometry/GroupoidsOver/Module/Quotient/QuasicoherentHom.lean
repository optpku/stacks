/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quotient.Comparison
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation

/-!
# Morphisms from quasi-coherent modules on quotient stacks

For flat, locally finitely presented groupoids in algebraic spaces, atlas
restriction is injective on morphisms from a quasi-coherent module to an
arbitrary module. Its image is characterized by the canonical comparison diagram.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
variable (F : QCoh (SmallQuotient.quotientStack G))
variable (H : RingedSite.ModuleCat.{u} (ringedSite (SmallQuotient.quotientStack G)))

/-- Restriction along the atlas of a quotient stack is injective on morphisms
from a quasi-coherent module to an arbitrary module when the source and target
maps of the groupoid are flat and locally of finite presentation. -/
theorem atlasRestrictHom_injective
    [AlgebraicSpace.Flat G.s.left]
    [AlgebraicSpace.LocallyOfFinitePresentation G.s.left]
    [AlgebraicSpace.Flat G.t.left]
    [AlgebraicSpace.LocallyOfFinitePresentation G.t.left] :
    Function.Injective (atlasRestrictHom G F.obj H) :=
  sorry

/-- A morphism of atlas restrictions from a quasi-coherent module to an arbitrary
module descends to the quotient stack exactly when it respects both canonical
comparison squares and their identification by the source–target isomorphism. -/
theorem mem_range_atlasRestrictHom_iff
    [AlgebraicSpace.Flat G.s.left]
    [AlgebraicSpace.LocallyOfFinitePresentation G.s.left]
    [AlgebraicSpace.Flat G.t.left]
    [AlgebraicSpace.LocallyOfFinitePresentation G.t.left]
    (φ : atlasRestrictModules G F.obj ⟶ atlasRestrictModules G H) :
    (∃ ψ : F.obj ⟶ H, atlasRestrictHom G F.obj H ψ = φ) ↔
      RespectsComparisons G F.obj H φ :=
  sorry

end AlgebraicGeometry.GroupoidsOver
