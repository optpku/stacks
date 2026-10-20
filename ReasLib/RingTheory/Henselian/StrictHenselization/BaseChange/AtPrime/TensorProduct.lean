module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.TensorProduct.Locality
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import ReasLib.RingTheory.Henselian.StrictHenselization.BaseChange.AtPrime.Admissible
public import ReasLib.RingTheory.Localization.AtPrime.TensorProduct.Comparison

@[expose] public section

/-!
# Strict-henselization consequences of tensor-prime comparison squares

The neutral tensor-prime comparison and residue-square APIs are owned by
`Localization.AtPrime.TensorProduct.Comparison`.  This leaf contains only the
consequences that use the four strict henselization hypotheses: lifting a
prescribed residue square, pure inseparability, and the tensor-product
bijectivity conclusion from Stacks Lemma 10.156.6.

@stack 0GIP
-/

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w x y z t

namespace IsStrictHenselizationOf.BaseChange.AtPrime.TensorProduct

open Localization.AtPrime.TensorProduct

section StrictHenselization

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C]
variable (pA : Ideal A) [pA.IsPrime]
variable (pB : Ideal B) [pB.IsPrime] [pB.LiesOver pA]
variable (pC : Ideal C) [pC.IsPrime]
variable (pD : Ideal (B ⊗[A] C)) [pD.IsPrime] [pD.LiesOver pB] [pD.LiesOver pC]
variable {Ash : Type x} {Bsh : Type y} {Csh : Type z} {Dsh : Type t}
variable [CommRing Ash] [CommRing Bsh] [CommRing Csh] [CommRing Dsh]
variable [Algebra (Localization.AtPrime pA) Ash]
variable [hAsh : IsStrictHenselizationOf (Localization.AtPrime pA) Ash]
variable [Algebra (Localization.AtPrime pB) Bsh]
variable [hBsh : IsStrictHenselizationOf (Localization.AtPrime pB) Bsh]
variable [Algebra (Localization.AtPrime pC) Csh]
variable [hCsh : IsStrictHenselizationOf (Localization.AtPrime pC) Csh]
variable [Algebra (Localization.AtPrime pD) Dsh]
variable [hDsh : IsStrictHenselizationOf (Localization.AtPrime pD) Dsh]

include hAsh hBsh hCsh hDsh in
/-- A coherent tensor-prime residue square has a propositionally unique
strict-henselization comparison realizing its four boundary maps.  The
comparison remains existential, so no arbitrary comparison map is selected as
public non-Prop data. -/
@[stacks 0GIP "strict-henselization comparison of a residue square"]
theorem ResidueSquare.existsUniqueComparison
    (residueSquare : Localization.AtPrime.TensorProduct.ResidueSquare
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh)) :
    ∃! comparison : Localization.AtPrime.TensorProduct.Comparison
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh),
      Localization.AtPrime.TensorProduct.ResidueSquare.IsRealizedBy pA pB pC pD
        residueSquare comparison := sorry

include hAsh hBsh hCsh hDsh in
/-- Tag 0GIP: the prescribed source-left residue-field map of a strict
henselization comparison is purely inseparable under the four source
admissibility alternatives. -/
@[stacks 0GIP "purely inseparable source-left residue map"]
theorem Comparison.residueSourceLeft_isPurelyInseparable
    (comparison : Localization.AtPrime.TensorProduct.Comparison
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh))
    (hB : IsAdmissible pA pB) :
    comparison.residueSourceLeft.IsPurelyInseparable := sorry

include hAsh hBsh hCsh hDsh in
/-- The tensor-product map of a strict-henselization comparison is bijective
when its prescribed source-left residue-field map is purely inseparable and
the source base-change map satisfies an admissibility alternative. -/
@[stacks 0GIP "tensor comparison from a purely inseparable residue map"]
theorem Comparison.tensorMap_bijective_of_purelyInseparable
    (comparison : Localization.AtPrime.TensorProduct.Comparison
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh))
    (hTau : comparison.residueSourceLeft.IsPurelyInseparable)
    (hB : IsAdmissible pA pB) :
    Function.Bijective (Localization.AtPrime.TensorProduct.Comparison.tensorMap
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh) comparison) := sorry

include hAsh hBsh hCsh hDsh in
/-- Tag 0GIP: the tensor-product map determined by an explicit strict
henselization comparison is bijective under the four source-faithful
admissibility alternatives. -/
@[stacks 0GIP "explicit strict-henselization comparison"]
theorem Comparison.tensorMap_bijective
    (comparison : Localization.AtPrime.TensorProduct.Comparison
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh))
    (hB : IsAdmissible pA pB) :
    Function.Bijective (Localization.AtPrime.TensorProduct.Comparison.tensorMap
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh) comparison) := sorry

include hAsh hBsh hCsh hDsh in
/-- Tag 0GIP: a coherent tensor-prime residue square lifts to a comparison
whose tensor-product map is bijective under any source admissibility
alternative.  This is the strict-henselization layer over the neutral
residue-square API. -/
@[stacks 0GIP "residue-square strict-henselization tensor comparison"]
theorem ResidueSquare.existsBijectiveComparison
    (residueSquare : Localization.AtPrime.TensorProduct.ResidueSquare
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh))
    (hB : IsAdmissible pA pB) :
    ∃ comparison : Localization.AtPrime.TensorProduct.Comparison
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh),
      Localization.AtPrime.TensorProduct.ResidueSquare.IsRealizedBy pA pB pC pD
        residueSquare comparison ∧
        Function.Bijective (Localization.AtPrime.TensorProduct.Comparison.tensorMap
          (pA := pA) (pB := pB) (pC := pC) (pD := pD)
          (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh) comparison) := sorry

end StrictHenselization

end IsStrictHenselizationOf.BaseChange.AtPrime.TensorProduct
