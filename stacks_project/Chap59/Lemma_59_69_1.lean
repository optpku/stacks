/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.EtaleCohomology.Curve
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.AssociatedModule
open AlgebraicGeometry.RelativePicard
open SheafOfModules.RingedSite

noncomputable section

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : SchemeOverField k) [Curve X] [Smooth X.hom] [Projective X.hom]
variable (n : ℕ)
variable (h_pos : 0 < n) (h_n : IsUnit (n : k))
variable (q : ℕ) (hq : 3 ≤ q)
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]

/- Lemma 59.69.1 (1): for a smooth projective curve over an algebraically closed field and an
invertible positive integer `n`, degree-zero étale cohomology with coefficients in `μₙ` is
identified with the additive presentation of `rootsOfUnity n k`. -/
@[stacks 03RQ] #check
  (AlgebraicGeometry.etaleCohomology_rootsOfUnity_h0 X n h_pos h_n :
    ((Sheaf.functorH X.left.smallEtaleTopology 0).obj
        (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
          (smallCommStructureSheaf .etale X.left) n)) ≃+
      Additive (rootsOfUnity n k))

/- Lemma 59.69.1 (2): in degree one, étale cohomology with coefficients in `μₙ` is identified
with the `n`-torsion of the degree-zero Picard subgroup. -/
@[stacks 03RQ] #check
  (AlgebraicGeometry.etaleCohomology_rootsOfUnity_h1 X n h_pos h_n :
    ((Sheaf.functorH X.left.smallEtaleTopology 1).obj
        (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
          (smallCommStructureSheaf .etale X.left) n)) ≃+
      AddSubgroup.torsionBy (degreeZeroClasses X) (n : ℤ))

/- Lemma 59.69.1 (3): the second étale cohomology group with coefficients in `μₙ` is identified
with `ZMod n`. -/
@[stacks 03RQ] #check
  (AlgebraicGeometry.etaleCohomology_rootsOfUnity_h2 X n h_pos h_n :
    ((Sheaf.functorH X.left.smallEtaleTopology 2).obj
        (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
          (smallCommStructureSheaf .etale X.left) n)) ≃+
      ZMod n)

/- Lemma 59.69.1 (4): étale cohomology with coefficients in `μₙ` vanishes in every degree at
least three. -/
@[stacks 03RQ] #check
  (AlgebraicGeometry.etaleCohomology_rootsOfUnity_isZero X n h_pos h_n q hq :
    IsZero
      ((Sheaf.functorH X.left.smallEtaleTopology q).obj
        (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
          (smallCommStructureSheaf .etale X.left) n)))

/- Lemma 59.69.1 (5): after identifying `μₙ` with the constant coefficient sheaf, degree-zero
étale cohomology is noncanonically identified with `ZMod n`. -/
@[stacks 03RQ] #check
  (AlgebraicGeometry.etaleCohomology_constantZMod_h0 X n h_pos h_n :
    Nonempty
      (((Sheaf.functorH X.left.smallEtaleTopology 0).obj
        ((constantSheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))))) ≃+
        ZMod n))

/- Lemma 59.69.1 (6): degree-one étale cohomology with constant `ZMod n` coefficients is
noncanonically identified with `(ZMod n)^(2g)`. -/
@[stacks 03RQ] #check
  (AlgebraicGeometry.etaleCohomology_constantZMod_h1 X n :
    ∀ (g : ℕ), AlgebraicGeometry.Curve.genus X = g → 0 < n → IsUnit (n : k) →
      Nonempty
        (((Sheaf.functorH X.left.smallEtaleTopology 1).obj
          ((constantSheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))))) ≃+
          (Fin (2 * g) → ZMod n)))

/- Lemma 59.69.1 (7): second étale cohomology with constant `ZMod n` coefficients is
noncanonically identified with `ZMod n`. -/
@[stacks 03RQ] #check
  (AlgebraicGeometry.etaleCohomology_constantZMod_h2 X n h_pos h_n :
    Nonempty
      (((Sheaf.functorH X.left.smallEtaleTopology 2).obj
        ((constantSheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))))) ≃+
        ZMod n))

/- Lemma 59.69.1 (8): étale cohomology with constant `ZMod n` coefficients vanishes in every
degree at least three. -/
@[stacks 03RQ] #check
  (AlgebraicGeometry.etaleCohomology_constantZMod_isZero X n h_pos h_n q hq :
    IsZero
      ((Sheaf.functorH X.left.smallEtaleTopology q).obj
        ((constantSheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))))))

end

end
