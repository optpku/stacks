/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Henselization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField
public import Mathlib.Topology.Inseparable

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- A specialization of points of a scheme lifts to a point of a chosen strict
henselization over the specializing point. -/
theorem existsPointOverSpecialization (S : Scheme.{u}) (t s : S)
    (tbar sbar : Scheme.GeometricPoint S)
    (Rsh : Type u) [CommRing Rsh] [Algebra (S.presheaf.stalk sbar.image) Rsh]
    [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) Rsh]
    (ht : tbar.image = t) (hs : sbar.image = s) (hSpec : Specializes t s) :
    ∃ t' : strictHenselizationScheme S sbar Rsh,
      strictHenselizationMap S sbar Rsh t' = t := sorry

/-- The residue field of a point lifted to a strict henselization is algebraic
and separable over the residue field of its image. -/
theorem residueFieldIsAlgebraicSeparable (S : Scheme.{u}) (sbar : Scheme.GeometricPoint S)
    (Rsh : Type u) [CommRing Rsh] [Algebra (S.presheaf.stalk sbar.image) Rsh]
    [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) Rsh]
    (t' : strictHenselizationScheme S sbar Rsh) :
    Algebra.IsAlgebraic
        (S.residueField (strictHenselizationMap S sbar Rsh t'))
        ((strictHenselizationScheme S sbar Rsh).residueField t') ∧
      Algebra.IsSeparable
        (S.residueField (strictHenselizationMap S sbar Rsh t'))
        ((strictHenselizationScheme S sbar Rsh).residueField t') := sorry

/-- A specialization of geometric points admits compatible maps into a chosen
strict henselization, with the lifted points specializing in the same direction. -/
theorem existsGeometricLift (S : Scheme.{u}) (t s : S)
    (tbar sbar : Scheme.GeometricPoint S)
    (Rsh : Type u) [CommRing Rsh] [Algebra (S.presheaf.stalk sbar.image) Rsh]
    [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) Rsh]
    (ht : tbar.image = t) (hs : sbar.image = s) (hSpec : Specializes t s) :
    ∃ u : Spec (.of tbar.K) ⟶ strictHenselizationScheme S sbar Rsh,
      ∃ v : Spec (.of sbar.K) ⟶ strictHenselizationScheme S sbar Rsh,
        u ≫ strictHenselizationMap S sbar Rsh = tbar.hom ∧
          v ≫ strictHenselizationMap S sbar Rsh = sbar.hom ∧
            Specializes (u default) (v default) := sorry

end AlgebraicGeometry.Scheme

end
