/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Henselization

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.Scheme

/- The strict-henselization map is provided by the canonical reusable owner. -/
#check (AlgebraicGeometry.Scheme.strictHenselizationMap :
  ∀ (S : Scheme.{u}) (sbar : Scheme.GeometricPoint S) (Rsh : Type u)
    [CommRing Rsh] [Algebra (S.presheaf.stalk sbar.image) Rsh]
    [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) Rsh],
    strictHenselizationScheme S sbar Rsh ⟶ S)

/- The defining equality for the strict-henselization map is provided by the canonical owner. -/
#check (AlgebraicGeometry.Scheme.strictHenselizationMap_def :
  ∀ (S : Scheme.{u}) (sbar : Scheme.GeometricPoint S) (Rsh : Type u)
    [CommRing Rsh] [Algebra (S.presheaf.stalk sbar.image) Rsh]
    [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) Rsh],
    strictHenselizationMap S sbar Rsh =
      Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk sbar.image) Rsh)) ≫
        S.fromSpecStalk sbar.image)

end AlgebraicGeometry.Scheme

end
