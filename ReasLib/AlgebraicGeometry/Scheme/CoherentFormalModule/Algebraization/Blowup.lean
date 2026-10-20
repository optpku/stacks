/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Inequalities
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.Target
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Intrinsic

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- A coherent formal module on the open complement in a Noetherian affine
scheme extends to the ambient scheme if the ring admits a dualizing complex,
the blowup of the defining ideal has fibres of dimension less than `d`, and
either the ordinary `(d + 1, d + 2)`-inequalities or the strict completed-stalk
depth-plus-dimension-plus-distance bound holds. -/
theorem extendsTo_of_blowup
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (S : AffineAlgebraizationSetup A)
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A),
        CategoryTheory.DerivedCategory.IsDualizing K)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    {X' : Scheme} (b : X' ⟶ S.X)
    [IsBlowup b (Scheme.idealSheafDataOfIdealOnSpec S.I)]
    (d : ℕ)
    (hdim : ∀ x : S.X, b.fiberDimension x < (d : WithBot ℕ∞))
    (h_alternative :
      SatisfiesInequalities S F ((d : ℤ) + 1) ((d : ℤ) + 2) ∨
        ∀ y : S.Y, (hy : S.y y ∈ S.U) →
          let yU := closedFiberOpenPoint S y hy
          ∀ p : PrimeSpectrum (completedLocalRing S yU),
            p ∉ PrimeSpectrum.zeroLocus
                (completedIdeal S yU : Set (completedLocalRing S yU)) →
              let depth : EInt := enatToEInt <|
                moduleDepth (Localization.AtPrime p.asIdeal)
                  (LocalizedModule.AtPrime p.asIdeal (completedStalk S F yU))
              let δ : EInt := enatToEInt (algebraizationDistance S y)
              (((d : ℤ) + 2 : ℤ) : EInt) <
                depth +
                    WithBot.map (WithTop.map Int.ofNat)
                      (ringKrullDim (completedLocalRing S yU ⧸ p.asIdeal)) +
                  δ) :
    extendsTo (Scheme.idealSheafDataOfIdealOnSpec S.I) S.U F := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
