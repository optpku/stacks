/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AdicSpfSquare

/-!
# Adic formal-spectrum test diagrams

A complete discrete valuation ring and an adic formal-spectrum test map form
a solid square. Its extensions carry an actual extension ring and a commuting lift.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

#check (AlgebraicGeometry.FormalAlgebraicSpace.AdicSpfSquare :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}, (X ⟶ Y) → Type (u + 1))

#check (AlgebraicGeometry.FormalAlgebraicSpace.AdicSpfSquare.of :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsCompleteLocalRing R] (structureHom : Spec (.of R) ⟶ S)
    (p : spf R structureHom ⟶ Y)
    (_ : AlgebraicSpace.representableByAlgebraicSpaces p), AdicSpfSquare f)

#check (AlgebraicGeometry.FormalAlgebraicSpace.AdicSpfSquare.specSpf :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (_ : AdicSpfSquare f), (Over S)ᵒᵖ ⥤ Type u)

#check (AlgebraicGeometry.FormalAlgebraicSpace.AdicSpfSquare.Extension :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (_ : AdicSpfSquare f), Type (u + 1))

#check (AlgebraicGeometry.FormalAlgebraicSpace.AdicSpfSquare.Extension.spec :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    {sq : AdicSpfSquare f} (e : sq.Extension), e.lift ≫ f = e.verticalMap ≫ sq.p)
