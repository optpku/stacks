/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Henselization.Specialization

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.Scheme

/- Remark 59.75.3 (Lifting specializations) - the point-lifting assertion. -/
@[stacks 0GJ5] #check
  (AlgebraicGeometry.Scheme.existsPointOverSpecialization :
    ∀ (S : Scheme.{u}) (t s : S) (tbar sbar : Scheme.GeometricPoint S)
      (Rsh : Type u) [CommRing Rsh] [Algebra (S.presheaf.stalk sbar.image) Rsh]
      [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) Rsh],
      tbar.image = t → sbar.image = s → Specializes t s →
        ∃ t' : strictHenselizationScheme S sbar Rsh,
          strictHenselizationMap S sbar Rsh t' = t)

/- Remark 59.75.3 (Lifting specializations) - the residue-field assertion. -/
@[stacks 0GJ5] #check
  (AlgebraicGeometry.Scheme.residueFieldIsAlgebraicSeparable :
    ∀ (S : Scheme.{u}) (sbar : Scheme.GeometricPoint S)
      (Rsh : Type u) [CommRing Rsh] [Algebra (S.presheaf.stalk sbar.image) Rsh]
      [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) Rsh]
      (t' : strictHenselizationScheme S sbar Rsh),
      Algebra.IsAlgebraic
          (S.residueField (strictHenselizationMap S sbar Rsh t'))
          ((strictHenselizationScheme S sbar Rsh).residueField t') ∧
        Algebra.IsSeparable
          (S.residueField (strictHenselizationMap S sbar Rsh t'))
          ((strictHenselizationScheme S sbar Rsh).residueField t'))

/- Remark 59.75.3 (Lifting specializations) - the geometric lifting assertion. -/
@[stacks 0GJ5] #check
  (AlgebraicGeometry.Scheme.existsGeometricLift :
    ∀ (S : Scheme.{u}) (t s : S) (tbar sbar : Scheme.GeometricPoint S)
      (Rsh : Type u) [CommRing Rsh] [Algebra (S.presheaf.stalk sbar.image) Rsh]
      [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) Rsh],
      tbar.image = t → sbar.image = s → Specializes t s →
        ∃ u : Spec (.of tbar.K) ⟶ strictHenselizationScheme S sbar Rsh,
          ∃ v : Spec (.of sbar.K) ⟶ strictHenselizationScheme S sbar Rsh,
            u ≫ strictHenselizationMap S sbar Rsh = tbar.hom ∧
              v ≫ strictHenselizationMap S sbar Rsh = sbar.hom ∧
                Specializes (u default) (v default))

end AlgebraicGeometry.Scheme

end
