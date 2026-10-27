/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Picard.Relative.Representability

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativePicard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The relative Picard functor of a flat, finitely presented, proper morphism
preserving the structure sheaf after every scheme-valued base change is locally
of finite presentation over the base. -/
theorem isLocallyOfFinitePresentationOver (f : X ⟶ B)
    [Flat f] [FinitePresentation f] [Proper f]
    [Hom.IsIsoBaseChangeStructurePushforward f] :
    IsLocallyOfFinitePresentationOver (picardFunctor f).obj := sorry

/-- A morphism representing the relative Picard functor of a flat, finitely
presented, proper morphism preserving the structure sheaf after every
scheme-valued base change is locally of finite presentation. -/
theorem isLocallyOfFinitePresentationOver_of_representable (f : X ⟶ B)
    [Flat f] [FinitePresentation f] [Proper f]
    [Hom.IsIsoBaseChangeStructurePushforward f] {Y : AlgebraicSpace S}
    {π : Y ⟶ B} (e : (picardFunctor f).obj ≅ yonedaOver π) :
    LocallyOfFinitePresentation π := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativePicard
