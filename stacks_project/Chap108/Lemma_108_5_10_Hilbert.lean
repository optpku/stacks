/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Hilbert
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ToSpec
public import stacks_project.Chap99.«99_7_1_1_Functor»

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/-- Direct image from the étale module site of a representable algebraic space to the
module category of its underlying scheme. -/
abbrev ofOverToScheme {S : Scheme.{u}} (U : Over S) :
    (ofOver U).Modules ⥤ U.left.Modules :=
  Modules.toScheme U

end AlgebraicGeometry.AlgebraicSpace.Quot

/- The Hilbert-polynomial locus inside the proper-support Quot functor. -/
#check (AlgebraicGeometry.AlgebraicSpace.Quot.quotHilbert :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [FinitePresentation f] [Separated f] (F L : X.Modules)
    [F.IsQuasicoherent] [isInvertibleObject L] (P : ℤ → ℤ),
    Subfunctor (AlgebraicGeometry.AlgebraicSpace.Quot.quot f F))
