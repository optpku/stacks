/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.FundamentalGroup
public import ReasLib.RingTheory.Henselian.FaithfullyFlat
public import ReasLib.RingTheory.Normal.Local
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.GeometricPoint

/-- For a normal local ring and its strict henselization, the fraction-field
fundamental-group sequence is exact, with kernel the closed normal closure of
the first map's image. -/
theorem strictHenselizationExact
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNormalRing A]
    {Ash : Type u} [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
    [IsDomain Ash]
    (ηbar : GeometricPoint (Spec (CommRingCat.of (FractionRing Ash)))) :
    let iK :=
      Spec.map (CommRingCat.ofHom
        (IsFractionRing.map (K := FractionRing A) (L := FractionRing Ash)
          (j := algebraMap A Ash)
          (RingHom.FaithfullyFlat.injective
            (IsStrictHenselizationOf.faithfullyFlat (R := A) (S := Ash)))))
    let iX := Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))
    let h' := fundamentalGroupMap iK ηbar
    let h := fundamentalGroupMap iX (map ηbar iK)
    Function.Surjective h ∧
      h.comp h' = 1 ∧
      MonoidHom.ker h.toMonoidHom =
        (Subgroup.normalClosure
          (MonoidHom.range h'.toMonoidHom : Set _)).topologicalClosure := sorry

end AlgebraicGeometry.Scheme.GeometricPoint
