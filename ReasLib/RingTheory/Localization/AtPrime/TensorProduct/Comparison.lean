/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.TensorProduct.ResidueCompatible
public import ReasLib.RingTheory.Algebra.TensorProduct.RingHom
public import ReasLib.RingTheory.Localization.AtPrime.TensorProduct

@[expose] public section

/-!
# Residue-compatible comparison squares at a tensor prime

This leaf owns coherent squares of local ring maps at the four localizations
determined by a prime of a tensor product.  Its public object is expressed in
raw ring maps, locality, scalar squares, and prescribed residue-field maps.
The noncanonical scalar structures selected by the tensor prime are installed
only in one private scalar-context bridge to the generic tensor-product API;
the public comparison surface never asks consumers to rebuild those instances.

@stack 0GIP
-/

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w x y z t

namespace Localization.AtPrime.TensorProduct

open Algebra.TensorProduct.ResidueCompatible

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
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

/-- Tag 0GIP: a coherent square of local maps over the four localizations
attached to a tensor prime.  The public fields use only canonical scalar maps;
the comparison-induced scalar presentation of the tensor product is private. -/
@[stacks 0GIP "tensor-prime local comparison square"]
structure Comparison where
  /-- The prescribed residue-field map on the source-to-left edge. -/
  residueSourceLeft : IsLocalRing.ResidueField Ash →+* IsLocalRing.ResidueField Bsh
  /-- The prescribed residue-field map on the source-to-right edge. -/
  residueSourceRight : IsLocalRing.ResidueField Ash →+* IsLocalRing.ResidueField Csh
  /-- The prescribed residue-field map on the left-to-target edge. -/
  residueLeftTarget : IsLocalRing.ResidueField Bsh →+* IsLocalRing.ResidueField Dsh
  /-- The prescribed residue-field map on the right-to-target edge. -/
  residueRightTarget : IsLocalRing.ResidueField Csh →+* IsLocalRing.ResidueField Dsh
  /-- The raw local map on the source-to-left edge. -/
  sourceLeft : Ash →+* Bsh
  /-- The raw local map on the source-to-right edge. -/
  sourceRight : Ash →+* Csh
  /-- The raw local map on the left-to-target edge. -/
  leftTarget : Bsh →+* Dsh
  /-- The raw local map on the right-to-target edge. -/
  rightTarget : Csh →+* Dsh
  /-- The source-to-left edge is local. -/
  sourceLeft_isLocal : IsLocalHom sourceLeft
  /-- The source-to-right edge is local. -/
  sourceRight_isLocal : IsLocalHom sourceRight
  /-- The left-to-target edge is local. -/
  leftTarget_isLocal : IsLocalHom leftTarget
  /-- The right-to-target edge is local. -/
  rightTarget_isLocal : IsLocalHom rightTarget
  /-- The source-to-left edge respects the tensor-prime localization scalar map. -/
  sourceLeft_scalar :
    sourceLeft.comp (algebraMap (Localization.AtPrime pA) Ash) =
      (algebraMap (Localization.AtPrime pB) Bsh).comp
        (Edge.sourceLeft (pA := pA) (pB := pB))
  /-- The source-to-right edge respects the tensor-prime localization scalar map. -/
  sourceRight_scalar :
    sourceRight.comp (algebraMap (Localization.AtPrime pA) Ash) =
      (algebraMap (Localization.AtPrime pC) Csh).comp
        (Edge.sourceRight (pA := pA) (pB := pB) (pC := pC) (pD := pD))
  /-- The left-to-target edge respects the tensor-prime localization scalar map. -/
  leftTarget_scalar :
    leftTarget.comp (algebraMap (Localization.AtPrime pB) Bsh) =
      (algebraMap (Localization.AtPrime pD) Dsh).comp
        (Edge.leftTarget (pB := pB) (pD := pD))
  /-- The right-to-target edge respects the tensor-prime localization scalar map. -/
  rightTarget_scalar :
    rightTarget.comp (algebraMap (Localization.AtPrime pC) Csh) =
      (algebraMap (Localization.AtPrime pD) Dsh).comp
        (Edge.rightTarget (pC := pC) (pD := pD))
  /-- The source-to-left residue square commutes. -/
  sourceLeft_residue :
    (IsLocalRing.residue Bsh).comp sourceLeft =
      residueSourceLeft.comp (IsLocalRing.residue Ash)
  /-- The source-to-right residue square commutes. -/
  sourceRight_residue :
    (IsLocalRing.residue Csh).comp sourceRight =
      residueSourceRight.comp (IsLocalRing.residue Ash)
  /-- The left-to-target residue square commutes. -/
  leftTarget_residue :
    (IsLocalRing.residue Dsh).comp leftTarget =
      residueLeftTarget.comp (IsLocalRing.residue Bsh)
  /-- The right-to-target residue square commutes. -/
  rightTarget_residue :
    (IsLocalRing.residue Dsh).comp rightTarget =
      residueRightTarget.comp (IsLocalRing.residue Csh)
  /-- The two raw routes from the source to the tensor-prime target agree. -/
  comm : leftTarget.comp sourceLeft = rightTarget.comp sourceRight

/-- Tag 0GIP: the raw commutative ring-hom square underlying a tensor-prime
local comparison.  It forgets only the local, scalar, and residue-field
compatibility data while preserving the four maps and their diagonal. -/
@[stacks 0GIP "raw square of a tensor-prime comparison"]
def Comparison.toRingHomSquare
    (comparison : Comparison
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh)) :
    Algebra.TensorProduct.RingHom.Square (X := Ash) (Y := Bsh) (Z := Csh) (W := Dsh) where
  sourceLeft := comparison.sourceLeft
  sourceRight := comparison.sourceRight
  leftTarget := comparison.leftTarget
  rightTarget := comparison.rightTarget
  comm := comparison.comm

/-- The source-facing name for the generic raw tensor map of a
tensor-prime comparison. -/
@[stacks 0GIP "tensor map of a tensor-prime comparison"]
noncomputable abbrev Comparison.tensorMap
    (comparison : Comparison
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh)) :
    comparison.toRingHomSquare.tensor →+* Dsh :=
  comparison.toRingHomSquare.map

/- The source-facing calculation rules keep consumers from unfolding the
generic raw-square owner merely to evaluate a comparison map. -/

/-- The tensor map of a tensor-prime comparison evaluates a pure tensor by the
two boundary maps. -/
@[simp, stacks 0GIP "tensor-prime comparison map on pure tensors"]
theorem Comparison.tensorMap_tmul
    (comparison : Comparison
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh))
    (b : Bsh) (c : Csh) :
    (Comparison.tensorMap pA pB pC pD comparison)
        ((Comparison.toRingHomSquare pA pB pC pD comparison).tmul b c) =
      comparison.leftTarget b * comparison.rightTarget c := sorry

/-- The tensor map of a tensor-prime comparison restricts to its left boundary
map. -/
@[stacks 0GIP "tensor-prime comparison left inclusion"]
theorem Comparison.tensorMap_comp_includeLeft
    (comparison : Comparison
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh)) :
    (Comparison.tensorMap pA pB pC pD comparison).comp
        (Comparison.toRingHomSquare pA pB pC pD comparison).includeLeft =
      comparison.leftTarget := sorry

/-- The tensor map of a tensor-prime comparison restricts to its right boundary
map. -/
@[stacks 0GIP "tensor-prime comparison right inclusion"]
theorem Comparison.tensorMap_comp_includeRight
    (comparison : Comparison
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh)) :
    (Comparison.tensorMap pA pB pC pD comparison).comp
        (Comparison.toRingHomSquare pA pB pC pD comparison).includeRight =
      comparison.rightTarget := sorry

/-- The source-facing ring equivalence obtained from a bijective tensor map
of a tensor-prime comparison. -/
@[stacks 0GIP "tensor equivalence of a tensor-prime comparison"]
noncomputable abbrev Comparison.tensorEquiv
    (comparison : Comparison
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh))
    (h : Function.Bijective (Comparison.tensorMap pA pB pC pD comparison)) :
    (Comparison.toRingHomSquare pA pB pC pD comparison).tensor ≃+* Dsh :=
  (Comparison.toRingHomSquare pA pB pC pD comparison).equiv h

section ResidueSquare

variable [IsLocalHom (algebraMap (Localization.AtPrime pA) Ash)]
variable [IsLocalHom (algebraMap (Localization.AtPrime pB) Bsh)]
variable [IsLocalHom (algebraMap (Localization.AtPrime pC) Csh)]
variable [IsLocalHom (algebraMap (Localization.AtPrime pD) Dsh)]

/-- Tag 0GIP: prescribed residue-field boundary data over the four localized
rings of a tensor-prime diagram.  A comparison realizing this data remains a
separate proposition-level conclusion. -/
@[stacks 0GIP "tensor-prime residue square"]
structure ResidueSquare where
  /-- The prescribed residue-field map from the source target to the left target. -/
  sourceLeft : IsLocalRing.ResidueField Ash →+* IsLocalRing.ResidueField Bsh
  /-- The prescribed residue-field map from the source target to the right target. -/
  sourceRight : IsLocalRing.ResidueField Ash →+* IsLocalRing.ResidueField Csh
  /-- The prescribed residue-field map from the left target to the tensor-prime target. -/
  leftTarget : IsLocalRing.ResidueField Bsh →+* IsLocalRing.ResidueField Dsh
  /-- The prescribed residue-field map from the right target to the tensor-prime target. -/
  rightTarget : IsLocalRing.ResidueField Csh →+* IsLocalRing.ResidueField Dsh
  /-- The source-left residue map is compatible with the named source-left edge. -/
  sourceLeft_comm :
    IsLocalRing.ResidueField.Compatible
      (Edge.sourceLeft (pA := pA) (pB := pB))
      (algebraMap (Localization.AtPrime pA) Ash)
      (algebraMap (Localization.AtPrime pB) Bsh) sourceLeft
  /-- The source-right residue map is compatible with the named source-right edge. -/
  sourceRight_comm :
    IsLocalRing.ResidueField.Compatible
      (Edge.sourceRight (pA := pA) (pB := pB) (pC := pC) (pD := pD))
      (algebraMap (Localization.AtPrime pA) Ash)
      (algebraMap (Localization.AtPrime pC) Csh) sourceRight
  /-- The left-target residue map is compatible with the named left-target edge. -/
  leftTarget_comm :
    IsLocalRing.ResidueField.Compatible
      (Edge.leftTarget (pB := pB) (pD := pD))
      (algebraMap (Localization.AtPrime pB) Bsh)
      (algebraMap (Localization.AtPrime pD) Dsh) leftTarget
  /-- The right-target residue map is compatible with the named right-target edge. -/
  rightTarget_comm :
    IsLocalRing.ResidueField.Compatible
      (Edge.rightTarget (pC := pC) (pD := pD))
      (algebraMap (Localization.AtPrime pC) Csh)
      (algebraMap (Localization.AtPrime pD) Dsh) rightTarget
  /-- The two residue-field routes from the source target to the tensor-prime target agree. -/
  comm : leftTarget.comp sourceLeft = rightTarget.comp sourceRight

/-- A local comparison square realizes prescribed residue data when its four
prescribed residue-field maps are the four displayed boundary maps. -/
@[stacks 0GIP "residue-square realization by a tensor-prime comparison"]
def ResidueSquare.IsRealizedBy
    (square : ResidueSquare
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh))
    (comparison : Comparison
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh)) : Prop :=
  comparison.residueSourceLeft = square.sourceLeft ∧
    comparison.residueSourceRight = square.sourceRight ∧
      comparison.residueLeftTarget = square.leftTarget ∧
        comparison.residueRightTarget = square.rightTarget

/-- Extract the residue-field boundary data induced by a local tensor-prime
comparison.  Its map fields are the comparison's prescribed residue maps;
compatibility is supplied through the private scalar-aware bridge. -/
@[stacks 0GIP "residue square of a tensor-prime comparison"]
noncomputable def Comparison.toResidueSquare
    (comparison : Comparison
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh)) :
    ResidueSquare
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh) :=
  { sourceLeft := comparison.residueSourceLeft
    sourceRight := comparison.residueSourceRight
    leftTarget := comparison.residueLeftTarget
    rightTarget := comparison.residueRightTarget
    sourceLeft_comm := sorry
    sourceRight_comm := sorry
    leftTarget_comm := sorry
    rightTarget_comm := sorry
    comm := sorry }

/-- The source-left map of `Comparison.toResidueSquare` is the comparison's
prescribed source-left residue-field map. -/
@[simp, stacks 0GIP "source-left projection of a comparison residue square"]
theorem Comparison.toResidueSquare_sourceLeft
    (comparison : Comparison
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh)) :
    (Comparison.toResidueSquare pA pB pC pD comparison).sourceLeft =
      comparison.residueSourceLeft := sorry

/-- The source-right map of `Comparison.toResidueSquare` is the comparison's
prescribed source-right residue-field map. -/
@[simp, stacks 0GIP "source-right projection of a comparison residue square"]
theorem Comparison.toResidueSquare_sourceRight
    (comparison : Comparison
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh)) :
    (Comparison.toResidueSquare pA pB pC pD comparison).sourceRight =
      comparison.residueSourceRight := sorry

/-- The left-target map of `Comparison.toResidueSquare` is the comparison's
prescribed left-target residue-field map. -/
@[simp, stacks 0GIP "left-target projection of a comparison residue square"]
theorem Comparison.toResidueSquare_leftTarget
    (comparison : Comparison
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh)) :
    (Comparison.toResidueSquare pA pB pC pD comparison).leftTarget =
      comparison.residueLeftTarget := sorry

/-- The right-target map of `Comparison.toResidueSquare` is the comparison's
prescribed right-target residue-field map. -/
@[simp, stacks 0GIP "right-target projection of a comparison residue square"]
theorem Comparison.toResidueSquare_rightTarget
    (comparison : Comparison
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh)) :
    (Comparison.toResidueSquare pA pB pC pD comparison).rightTarget =
      comparison.residueRightTarget := sorry

/-- A comparison realizes the residue square extracted from its own four
prescribed boundary maps. -/
@[stacks 0GIP "self-realization of a tensor-prime residue square"]
theorem ResidueSquare.isRealizedBy_toResidueSquare
    (comparison : Comparison
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh)) :
    ResidueSquare.IsRealizedBy pA pB pC pD
      (Comparison.toResidueSquare pA pB pC pD comparison) comparison := sorry

end ResidueSquare

end

end Localization.AtPrime.TensorProduct
