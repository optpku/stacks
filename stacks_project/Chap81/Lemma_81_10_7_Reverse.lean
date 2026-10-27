/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.FormalGlueing.Adjunction

/-!
# Reverse functor for formal glueing of quasi-coherent modules

The reverse kernel functor and its canonical unit and counit are provided by
the shared formal-glueing adjunction API.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing.reverse :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X),
    [IsClosedImmersion i] → [QuasiCompact f] → [QuasiSeparated f] →
    [FinitePresentation i] →
    AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing.category f i ⥤ QCoh X)

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing.unit :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X),
    [IsClosedImmersion i] → [QuasiCompact f] → [QuasiSeparated f] →
    [FinitePresentation i] →
    𝟭 (QCoh X) ⟶ AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing.functor f i ⋙
      AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing.reverse f i)

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing.counit :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X),
    [IsClosedImmersion i] → [QuasiCompact f] → [QuasiSeparated f] →
    [FinitePresentation i] →
    AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing.reverse f i ⋙
      AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing.functor f i ⟶
        𝟭 (AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing.category f i))
