/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Blowup
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.DenseOpen
import ReasLib.AlgebraicGeometry.Scheme.Blowup.Composition
import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Complement
import ReasLib.AlgebraicGeometry.Scheme.StrictTransform.Composition
import ReasLib.AlgebraicGeometry.Scheme.Topology.Retrocompact

/-!
# Open strict transforms after admissible blowups

This module records when an admissible blowup makes the strict transform of a scheme morphism
an open immersion.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A separated finite-type morphism that is an isomorphism over a quasi-compact open has an
open strict transform after a suitable admissible blowup away from that open. -/
theorem exists_isAdmissibleBlowup_strictTransform_isOpenImmersion
    {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) [IsSeparated f] [Scheme.Hom.FiniteType f]
    (U : S.Opens) [QuasiCompact U.ι] [IsIso (f ∣_ U)] :
    ∃ (S' : Scheme.{u}) (b : S' ⟶ S) (I : S.IdealSheafData),
      IsAdmissibleBlowupCenter U b I ∧
        IsOpenImmersion (strictTransformSnd b (I.comap b) f) := sorry

end AlgebraicGeometry
