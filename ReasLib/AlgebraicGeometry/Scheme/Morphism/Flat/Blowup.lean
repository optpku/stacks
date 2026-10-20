/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.StrictTransform.Blowup
import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Blowup

/-!
# Flattening scheme morphisms by admissible blowups

This module records the existence of admissible blowups that flatten strict transforms of
scheme morphisms.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A finite-type quasi-separated morphism that is flat and locally of finite presentation over
a quasi-compact open has a flat finitely presented strict transform after an admissible blowup
away from that open. -/
theorem exists_isAdmissibleBlowup_flattening
    {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) [Scheme.Hom.FiniteType f] [QuasiSeparated f]
    (U : S.Opens) [QuasiCompact U.ι]
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)] :
    ∃ (S' : Scheme.{u}) (b : S' ⟶ S) (I : S.IdealSheafData),
      IsAdmissibleBlowupCenter U b I ∧
        let f' := strictTransformSnd b (I.comap b) f
        Flat f' ∧ Scheme.Hom.FinitePresentation f' := sorry

end AlgebraicGeometry.Scheme.Hom
