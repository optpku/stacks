/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.LocalRing.ResidueField.Model
public import ReasLib.RingTheory.Localization.AtPrime.TensorProduct.Comparison

@[expose] public section

/-!
# Common-field models for tensor-prime residue squares

This leaf packages four relative separable-closure realizations in one field
over the localizations determined by a tensor prime.  It is independent of
strict henselizations: the model induces residue-field boundary data, while
any lifting of that data to more structured local objects belongs to a
downstream specialization.

@stack 0GIP
-/

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w x y z t r

namespace Localization.AtPrime.TensorProduct.CommonField

section

variable {A : Type u} {B : Type v} {C : Type w} {K : Type r}
variable [CommRing A] [CommRing B] [CommRing C] [Field K]
variable [Algebra A B] [Algebra A C]
variable (pA : Ideal A) [pA.IsPrime]
variable (pB : Ideal B) [pB.IsPrime] [pB.LiesOver pA]
variable (pC : Ideal C) [pC.IsPrime]
variable (pD : Ideal (B ⊗[A] C)) [pD.IsPrime] [pD.LiesOver pB] [pD.LiesOver pC]
variable {Ash : Type x} {Bsh : Type y} {Csh : Type z} {Dsh : Type t}
variable [CommRing Ash] [CommRing Bsh] [CommRing Csh] [CommRing Dsh]
variable [IsLocalRing Ash] [IsLocalRing Bsh] [IsLocalRing Csh] [IsLocalRing Dsh]
variable [Algebra (Localization.AtPrime pA) Ash]
variable [Algebra (Localization.AtPrime pB) Bsh]
variable [Algebra (Localization.AtPrime pC) Csh]
variable [Algebra (Localization.AtPrime pD) Dsh]
variable [IsLocalHom (algebraMap (Localization.AtPrime pA) Ash)]
variable [IsLocalHom (algebraMap (Localization.AtPrime pB) Bsh)]
variable [IsLocalHom (algebraMap (Localization.AtPrime pC) Csh)]
variable [IsLocalHom (algebraMap (Localization.AtPrime pD) Dsh)]

/-- Tag 0GIP: four relative separable-closure models in one common field over
the tensor-prime residue diagram.  The source's separably closed common field
is a special case; the package itself uses only the supplied field models and
their base-residue coherence. -/
@[stacks 0GIP "common-field residue model"]
structure Model where
  /-- The relative separable-closure model at the source prime. -/
  source : IsLocalRing.ResidueField.LocalModel (K := K)
    (algebraMap (Localization.AtPrime pA) Ash)
  /-- The relative separable-closure model at the left prime. -/
  left : IsLocalRing.ResidueField.LocalModel (K := K)
    (algebraMap (Localization.AtPrime pB) Bsh)
  /-- The relative separable-closure model at the right prime. -/
  right : IsLocalRing.ResidueField.LocalModel (K := K)
    (algebraMap (Localization.AtPrime pC) Csh)
  /-- The relative separable-closure model at the tensor prime. -/
  target : IsLocalRing.ResidueField.LocalModel (K := K)
    (algebraMap (Localization.AtPrime pD) Dsh)
  /-- The source and left base residue-field maps into the common field agree. -/
  sourceLeft_comm :
    left.residueMap.comp (ResidueField.sourceLeft (pA := pA) (pB := pB)) =
      source.residueMap
  /-- The source and right base residue-field maps into the common field agree. -/
  sourceRight_comm :
    right.residueMap.comp
        (ResidueField.sourceRight (pA := pA) (pB := pB) (pC := pC) (pD := pD)) =
      source.residueMap
  /-- The left and tensor-prime base residue-field maps into the common field agree. -/
  leftTarget_comm :
    target.residueMap.comp (ResidueField.leftTarget (pB := pB) (pD := pD)) =
      left.residueMap
  /-- The right and tensor-prime base residue-field maps into the common field agree. -/
  rightTarget_comm :
    target.residueMap.comp (ResidueField.rightTarget (pC := pC) (pD := pD)) =
      right.residueMap

namespace Model

/-- The four base-residue coherence conditions defining a common-field model. -/
@[stacks 0GIP "specification of a common-field residue model"]
theorem spec
    (model : Model
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh) (K := K)) :
    model.left.residueMap.comp (ResidueField.sourceLeft (pA := pA) (pB := pB)) =
        model.source.residueMap ∧
      model.right.residueMap.comp
          (ResidueField.sourceRight (pA := pA) (pB := pB) (pC := pC) (pD := pD)) =
        model.source.residueMap ∧
        model.target.residueMap.comp (ResidueField.leftTarget (pB := pB) (pD := pD)) =
          model.left.residueMap ∧
          model.target.residueMap.comp
              (ResidueField.rightTarget (pC := pC) (pD := pD)) =
            model.right.residueMap := sorry

/-- A prescribed tensor-prime residue square is induced by a common-field
model when each boundary map commutes with the corresponding realization map
into the common field. -/
@[stacks 0GIP "common-field realization of a residue square"]
noncomputable def induces
    (model : Model
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh) (K := K))
    (square : ResidueSquare
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh)) : Prop :=
  model.left.residueLift.comp square.sourceLeft = model.source.residueLift ∧
    model.right.residueLift.comp square.sourceRight = model.source.residueLift ∧
      model.target.residueLift.comp square.leftTarget = model.left.residueLift ∧
        model.target.residueLift.comp square.rightTarget = model.right.residueLift

/-- Unfold the four realization equations in `Model.induces`. -/
@[stacks 0GIP "common-field residue-square realization iff"]
theorem induces_iff
    (model : Model
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh) (K := K))
    (square : ResidueSquare
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh)) :
    Model.induces pA pB pC pD model square ↔
      model.left.residueLift.comp square.sourceLeft = model.source.residueLift ∧
        model.right.residueLift.comp square.sourceRight = model.source.residueLift ∧
          model.target.residueLift.comp square.leftTarget = model.left.residueLift ∧
            model.target.residueLift.comp square.rightTarget = model.right.residueLift := sorry

/-- The four local residue-field models in a common field induce a unique
coherent tensor-prime residue square. -/
@[stacks 0GIP "unique residue square from a common-field model"]
theorem existsUniqueSquare
    (model : Model
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh) (K := K)) :
    ∃! square : ResidueSquare
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh),
      Model.induces pA pB pC pD model square := sorry

end Model

end

end Localization.AtPrime.TensorProduct.CommonField
