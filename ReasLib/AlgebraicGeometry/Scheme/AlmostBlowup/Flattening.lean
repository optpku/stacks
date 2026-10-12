/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AlmostBlowup
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Blowup

/-!
# Flattening scheme morphisms by almost blowup squares

This module records the existence of compatible almost blowup squares that flatten strict
transforms of finitely presented scheme morphisms.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A finitely presented morphism that is flat over a quasi-compact open has compatible almost
blowup squares away from that open whose strict-transform morphism is flat and finitely
presented. -/
theorem exists_isAlmostBlowupSquare_flattening
    {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [Scheme.Hom.FinitePresentation f]
    (V : Y.Opens) [QuasiCompact V.ι] [Flat (f ∣_ V)] :
    ∃ (Y' : Scheme.{u}) (b : Y' ⟶ Y) (I : Y.IdealSheafData),
      IsAlmostBlowupSquare b I ∧
        IsAlmostBlowupSquare (strictTransformFst b (I.comap b) f) (I.comap f) ∧
        Disjoint (I.support : Set Y) V ∧
        Flat (strictTransformSnd b (I.comap b) f) ∧
        Scheme.Hom.FinitePresentation (strictTransformSnd b (I.comap b) f) := sorry

end AlgebraicGeometry.Scheme.Hom
