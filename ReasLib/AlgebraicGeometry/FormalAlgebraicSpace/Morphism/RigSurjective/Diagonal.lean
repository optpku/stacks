/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSurjective
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigEtale
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType.Diagonal

/-!
# Rig-surjectivity with a rig-étale, rig-surjective diagonal
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
  CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective

/-- A locally of finite type morphism of locally Noetherian formal algebraic
spaces whose relative diagonal is rig-étale and rig-surjective is rig-surjective
if and only if every adic morphism from the formal spectrum of a complete
discrete valuation ring lifts through it without extending the ring. -/
theorem iff_adicSpf_lifts {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [RigEtale (pullback.diagonal f)]
    [RigSurjective (pullback.diagonal f)] :
    RigSurjective f ↔
      ∀ sq : AdicSpfSquare f, ∃ lift : sq.specSpf ⟶ X, lift ≫ f = sq.p :=
  sorry

/-- A rig-surjective, locally of finite type morphism of locally Noetherian
formal algebraic spaces whose relative diagonal is rig-étale and rig-surjective
admits a lift of every adic morphism from the formal spectrum of a complete
discrete valuation ring without extending the ring. -/
theorem exists_lift {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [RigEtale (pullback.diagonal f)]
    [RigSurjective (pullback.diagonal f)] [RigSurjective f]
    (sq : AdicSpfSquare f) :
    ∃ lift : sq.specSpf ⟶ X, lift ≫ f = sq.p :=
  (iff_adicSpf_lifts f).mp inferInstance sq

end AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective
