/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.TensorProduct.RingHom
public import ReasLib.RingTheory.Localization.AtPrime.TensorProduct.CommonField
public import ReasLib.RingTheory.Localization.AtPrime.TensorProduct.ResidueField

@[expose] public section

/-!
# Common-field models realizing a tensor map

This leaf relates the raw field-valued tensor-product map in a common-field
construction to an already supplied `CommonField.Model`.  Generic tensor-map
restrictions are owned by `Algebra.TensorProduct.RingHom`; no raw map selects
maps between arbitrary strict henselizations here.

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

namespace Model

/-- Tag 0GIP: a common-field model realizes a raw tensor-product map when the
map is the composite of its target residue-field realization with the canonical
map to the tensor-prime residue field.  The other three factor/base
restrictions are consequences of model coherence. -/
@[stacks 0GIP "common-field model realizes a raw tensor map"]
def realizesTensorMap
    (model : Model
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh) (K := K))
    (map : B ⊗[A] C →+* K) : Prop :=
  map = Localization.AtPrime.TensorProduct.ResidueField.tensorMap
    (pD := pD) model.target.residueMap

/-- The left model's base residue map realizes the left-factor restriction of
a realized tensor map. -/
@[stacks 0GIP "common-field model left restriction"]
theorem realizesTensorMap_left
    {model : Model
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh) (K := K)}
    {map : B ⊗[A] C →+* K}
    (h : Model.realizesTensorMap pA pB pC pD model map) :
    model.left.residueMap.comp (algebraMap B pB.ResidueField) =
      Algebra.TensorProduct.RingHom.restrictLeft map := sorry

/-- The right model's base residue map realizes the right-factor restriction
of a realized tensor map. -/
@[stacks 0GIP "common-field model right restriction"]
theorem realizesTensorMap_right
    {model : Model
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh) (K := K)}
    {map : B ⊗[A] C →+* K}
    (h : Model.realizesTensorMap pA pB pC pD model map) :
    model.right.residueMap.comp (algebraMap C pC.ResidueField) =
      Algebra.TensorProduct.RingHom.restrictRight map := sorry

/-- The source model's base residue map realizes the base-ring restriction of
a realized tensor map. -/
@[stacks 0GIP "common-field model base restriction"]
theorem realizesTensorMap_base
    {model : Model
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh) (K := K)}
    {map : B ⊗[A] C →+* K}
    (h : Model.realizesTensorMap pA pB pC pD model map) :
    model.source.residueMap.comp (algebraMap A pA.ResidueField) =
      Algebra.TensorProduct.RingHom.restrictBase map := sorry

/-- A tensor map realized by a common-field model has the selected tensor
prime as its kernel. -/
@[stacks 0GIP "common-field model tensor-map kernel"]
theorem realizesTensorMap_ker
    {model : Model
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh) (K := K)}
    {map : B ⊗[A] C →+* K}
    (h : Model.realizesTensorMap pA pB pC pD model map) :
    RingHom.ker map = pD := sorry

/-- The left-factor restriction of a tensor map realized by a common-field
model has kernel `pB`. -/
@[stacks 0GIP "common-field model left kernel"]
theorem realizesTensorMap_left_ker
    {model : Model
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh) (K := K)}
    {map : B ⊗[A] C →+* K}
    (h : Model.realizesTensorMap pA pB pC pD model map) :
    RingHom.ker (Algebra.TensorProduct.RingHom.restrictLeft map) = pB := sorry

/-- The right-factor restriction of a tensor map realized by a common-field
model has kernel `pC`. -/
@[stacks 0GIP "common-field model right kernel"]
theorem realizesTensorMap_right_ker
    {model : Model
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh) (K := K)}
    {map : B ⊗[A] C →+* K}
    (h : Model.realizesTensorMap pA pB pC pD model map) :
    RingHom.ker (Algebra.TensorProduct.RingHom.restrictRight map) = pC := sorry

/-- The base-ring restriction of a tensor map realized by a common-field
model has kernel `pA`. -/
@[stacks 0GIP "common-field model base kernel"]
theorem realizesTensorMap_base_ker
    {model : Model
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh) (K := K)}
    {map : B ⊗[A] C →+* K}
    (h : Model.realizesTensorMap pA pB pC pD model map) :
    RingHom.ker (Algebra.TensorProduct.RingHom.restrictBase map) = pA := sorry

end Model

end

end Localization.AtPrime.TensorProduct.CommonField
