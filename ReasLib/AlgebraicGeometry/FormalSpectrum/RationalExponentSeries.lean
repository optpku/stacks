/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Valuation.RationalExponentSeries
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AdicSpfSquare
public import ReasLib.AlgebraicGeometry.FormalSpectrum.Colimit

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- The sheaf formal spectrum of the rational-exponent series ring admits no
adic complete discrete valuation ring test squares over any morphism into it. -/
theorem isEmpty_adicSpfSquare {κ : Type u} [Field κ] {S : Scheme.{u}}
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (structureHom : Spec (.of (RationalExponentSeries κ)) ⟶ S)
    {X : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ (AlgebraicGeometry.AffineFormalAlgebraicSpace.spf
      (RationalExponentSeries κ) structureHom).obj) :
    IsEmpty (AdicSpfSquare f) :=
  sorry

/-- Every morphism into the sheaf formal spectrum of the rational-exponent
series ring satisfies the complete discrete valuation ring lifting test vacuously. -/
theorem dvrTest_vacuous {κ : Type u} [Field κ] {S : Scheme.{u}}
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (structureHom : Spec (.of (RationalExponentSeries κ)) ⟶ S)
    {X : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ (AlgebraicGeometry.AffineFormalAlgebraicSpace.spf
      (RationalExponentSeries κ) structureHom).obj) :
    ∀ sq : AdicSpfSquare f, Nonempty sq.Extension := by
  intro sq
  exact ((isEmpty_adicSpfSquare structureHom f).false sq).elim

end AlgebraicGeometry.FormalAlgebraicSpace
