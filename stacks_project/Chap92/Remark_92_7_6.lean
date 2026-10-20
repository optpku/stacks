module

public import ReasLib.RingTheory.CotangentComplex.ResolutionComparison
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

/-!
# Canonical identification of `Ω_{Q̄_•/B} ⊗ C` with `Ω_{R_•/B} ⊗ C`

Remark 92.7.6 explains the comparison maps `Q̄_• → R̄_•` and `R_• → R̄_•` induced by
the functoriality square of standard resolutions, and records that the resulting
maps on naive differentials are quasi-isomorphisms whose derived-category composite
identifies `Ω_{Q̄_•/B} ⊗_{Q̄_•} C` with `Ω_{R_•/B} ⊗_{R_•} C`.
-/

@[expose] public section

open CategoryTheory
open Algebra
open Algebra.PolynomialSite
open Algebra.CotangentComplex

noncomputable section

universe u q

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

variable (n : SimplexCategoryᵒᵖ) (h_inj : Function.Injective (algebraMap B C))

/- Remark 92.7.6 (1): the standard term of `C` over `B` is polynomial over
that of `B` over `B` when `B → C` is injective. -/
@[stacks 08SE] #check (Algebra.CotangentComplex.isPolynomial_standardQ_over_standardP B B C n h_inj :
  IsPolynomial (Algebra.CotangentComplex.standardP B B n)
    (Algebra.CotangentComplex.standardQ B C n))

/- Remark 92.7.6 (2): the tensor base change of the standard resolutions over `B`
is a polynomial simplicial resolution of `C`. -/
@[stacks 08SE] #check (Algebra.CotangentComplex.isResolution_barQHom B B C h_inj :
  IsResolution (Algebra.CotangentComplex.barQHom B B C h_inj))

/- Remark 92.7.6 (3): the square of standard resolutions induces the canonical
comparison between their tensor base changes. -/
@[stacks 08SE] #check (Algebra.CotangentComplex.barQToBarR A B C h_inj :
  Algebra.CotangentComplex.barQSimplicial A B C h_inj ⟶
    Algebra.CotangentComplex.barQSimplicial B B C h_inj)

/- Remark 92.7.6 (4): the differential map induced by the left tensor inclusion
is a quasi-isomorphism. -/
@[stacks 08SE] #check (Algebra.CotangentComplex.omegaEvalToBarR_quasiIso B C h_inj :
  QuasiIso (Algebra.CotangentComplex.omegaEvalToBarR B C h_inj))

/- Remark 92.7.6 (5): the differential map induced by coefficient change
is a quasi-isomorphism. -/
@[stacks 08SE] #check (Algebra.CotangentComplex.omegaBarQToBarR_quasiIso A B C h_inj :
  QuasiIso (Algebra.CotangentComplex.omegaBarQToBarR A B C h_inj))

variable [HasDerivedCategory.{q} (ModuleCat.{u} C)]

/- Remark 92.7.6 (6): the differential comparison followed by the inverse of the
standard-resolution comparison gives the canonical identification in `D(C)`. -/
@[stacks 08SE] #check (Algebra.CotangentComplex.barQ_iso_omegaEval A B C h_inj :
  IsIso (DerivedCategory.Q.map (Algebra.CotangentComplex.omegaBarQToBarR A B C h_inj) ≫
    inv (DerivedCategory.Q.map (Algebra.CotangentComplex.omegaEvalToBarR B C h_inj))))
