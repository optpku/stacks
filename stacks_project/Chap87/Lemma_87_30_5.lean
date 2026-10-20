/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Separation.Locality
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 87.30.5: the five equivalent conditions for separatedness
of a morphism of formal algebraic spaces. -/
@[stacks 0ARS] #check (AlgebraicGeometry.FormalAlgebraicSpace.Separated.tfae :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace X]
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace Y] (f : X ⟶ Y),
    List.TFAE [AlgebraicGeometry.FormalAlgebraicSpace.Separated f,
      AlgebraicGeometry.FormalAlgebraicSpace.Separated.forallScheme f,
      AlgebraicGeometry.FormalAlgebraicSpace.Separated.forallAffine f,
      AlgebraicGeometry.FormalAlgebraicSpace.Separated.forallAffineSpace f,
      AlgebraicGeometry.FormalAlgebraicSpace.Separated.existsCoverOnTarget f])

/- Lemma 87.30.5: the five equivalent conditions for quasi-separatedness
of a morphism of formal algebraic spaces. -/
@[stacks 0ARS] #check (AlgebraicGeometry.FormalAlgebraicSpace.QuasiSeparated.tfae :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace X]
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace Y] (f : X ⟶ Y),
    List.TFAE [AlgebraicGeometry.FormalAlgebraicSpace.QuasiSeparated f,
      AlgebraicGeometry.FormalAlgebraicSpace.QuasiSeparated.forallScheme f,
      AlgebraicGeometry.FormalAlgebraicSpace.QuasiSeparated.forallAffine f,
      AlgebraicGeometry.FormalAlgebraicSpace.QuasiSeparated.forallAffineSpace f,
      AlgebraicGeometry.FormalAlgebraicSpace.QuasiSeparated.existsCoverOnTarget f])

