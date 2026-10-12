/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.RingTheory.RingHom.Flat
public import stacks_project.Chap92.Lemma_92_6_4
public import stacks_project.Chap92.Lemma_92_7_1
public import stacks_project.Chap92.Remark_92_7_5_Resolution
public import stacks_project.Chap92.«92_7_0_1_Triangle»
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

/-!
# Alternative construction of the fundamental triangle

Remark 92.7.5 records an alternative proof of the transitivity triangle: if `B → C` is
injective, the functorial standard resolutions yield a simplicial polynomial resolution
`Q̄_•` of `C` over `B`, and the Jacobi–Zariski sequence of simplicial `C`-modules
computes the distinguished triangle. The general case reduces to `A → B → B × C`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Algebra
open Algebra.PolynomialSite
open Algebra.CotangentComplex
open RingedSite.Cotangent
open RingedSite.Cotangent.PolynomialTriple
open HomologicalComplex
open AlgebraicTopology
open scoped TensorProduct

noncomputable section

universe u

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- Remark 92.7.5 (1): if `B → C` is injective, then each term `Q_n` of the standard
resolution of `C` over `A` is a polynomial algebra over the corresponding term `P_n` of
the standard resolution of `B` over `A`. -/
@[stacks 08SD]
theorem isPolynomial_standardQ_over_standardP_of_injective (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    IsPolynomial (standardP A B n) (standardQ A C n) :=
  isPolynomial_standardQ_over_standardP A B C n h_inj

/- Remark 92.7.5 (2): the pairs `(P_n → B, Q_n → C)` therefore assemble into a
cosimplicial object of the site `C_{C/B/A}`. -/
@[stacks 08SD] #check tripleCosimplicial

/- Remark 92.7.5 (3): the auxiliary simplicial `B`-algebra is
`Q̄_• = Q_• ⊗_{P_•} B`, with augmentation `barQHom`. -/
@[stacks 08SD] #check barQ
@[stacks 08SD] #check barQHom

/-- Remark 92.7.5 (4): `Q̄_•` is a resolution of `C` over `B`. -/
@[stacks 08SD]
theorem isResolution_barQ (h_inj : Function.Injective (algebraMap B C)) :
    IsResolution (barQHom A B C h_inj) :=
  isResolution_barQHom A B C h_inj

/-- Remark 92.7.5 (5): the Jacobi–Zariski sequence of the functorial triples is a short
exact sequence of `C`-modules in each simplicial degree
`0 → Ω_{P_n / A} ⊗_{P_n} C → Ω_{Q_n / A} ⊗_{Q_n} C → Ω_{Q̄_n / B} ⊗_{Q̄_n} C → 0`. -/
@[stacks 08SD]
theorem functorialOmegaSequence_shortExact (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    (omegaSequence_app A B C (triple A B C n h_inj)).ShortExact :=
  omegaSequence_app_shortExact A B C (triple A B C n h_inj)

/-- The simplicial `C`-module `Ω_{P_• / A} ⊗_{P_•} C`. -/
def omegaPSimplicial (h_inj : Function.Injective (algebraMap B C)) :
    SimplicialObject (ModuleCat.{u} C) :=
  tripleSimplicial A B C h_inj ⋙ tensorOmega1 A B C

/-- Degreewise, `omegaPSimplicial` evaluates `tensorOmega1` on the functorial triple. -/
theorem omegaPSimplicial_obj (h_inj : Function.Injective (algebraMap B C))
    (n : SimplexCategoryᵒᵖ) :
    (omegaPSimplicial A B C h_inj).obj n =
      (tensorOmega1 A B C).obj (triple A B C n h_inj) :=
  sorry

/-- The simplicial `C`-module `Ω_{Q_• / A} ⊗_{Q_•} C`. -/
def omegaQSimplicial (h_inj : Function.Injective (algebraMap B C)) :
    SimplicialObject (ModuleCat.{u} C) :=
  tripleSimplicial A B C h_inj ⋙ inverseImageOmega2 A B C

/-- Degreewise, `omegaQSimplicial` evaluates `inverseImageOmega2` on the functorial
triple. -/
theorem omegaQSimplicial_obj (h_inj : Function.Injective (algebraMap B C))
    (n : SimplexCategoryᵒᵖ) :
    (omegaQSimplicial A B C h_inj).obj n =
      (inverseImageOmega2 A B C).obj (triple A B C n h_inj) :=
  sorry

/-- The simplicial `C`-module `Ω_{Q̄_• / B} ⊗_{Q̄_•} C`. -/
def omegaBarQSimplicial (h_inj : Function.Injective (algebraMap B C)) :
    SimplicialObject (ModuleCat.{u} C) :=
  tripleSimplicial A B C h_inj ⋙ inverseImageOmega3 A B C

/-- Degreewise, `omegaBarQSimplicial` evaluates `inverseImageOmega3` on the functorial
triple. -/
theorem omegaBarQSimplicial_obj (h_inj : Function.Injective (algebraMap B C))
    (n : SimplexCategoryᵒᵖ) :
    (omegaBarQSimplicial A B C h_inj).obj n =
      (inverseImageOmega3 A B C).obj (triple A B C n h_inj) :=
  sorry

/-- The cochain complex of `C`-modules associated to `Ω_{Q̄_• / B} ⊗_{Q̄_•} C`. -/
def omegaBarQCochain (h_inj : Function.Injective (algebraMap B C)) :
    CochainComplex (ModuleCat.{u} C) ℤ :=
  ((alternatingFaceMapComplex (ModuleCat.{u} C)).obj
      (omegaBarQSimplicial A B C h_inj)).extend ComplexShape.embeddingDownNat

/-- Unfolding `omegaBarQCochain` recovers the extended alternating-face complex of
`omegaBarQSimplicial`. -/
theorem omegaBarQCochain_eq (h_inj : Function.Injective (algebraMap B C)) :
    omegaBarQCochain A B C h_inj =
      ((alternatingFaceMapComplex (ModuleCat.{u} C)).obj
          (omegaBarQSimplicial A B C h_inj)).extend ComplexShape.embeddingDownNat :=
  sorry

/-- Remark 92.7.5 (6): by Remark 92.5.5 and the resolution property of `Q̄_•`, the complex
`Ω_{Q̄_• / B} ⊗_{Q̄_•} C` represents `L_{C/B}` in `D(C)`. -/
@[stacks 08SD]
theorem barQ_represents_relative (h_inj : Function.Injective (algebraMap B C)) :
    IsIsomorphic (derived B C)
      (DerivedCategory.Q.obj (omegaBarQCochain A B C h_inj)) :=
  sorry

/-- The cochain complex associated to a simplicial `C`-module by the alternating-face
construction, extended to all cohomological degrees. -/
def simplicialModuleToCochain :
    SimplicialObject (ModuleCat.{u} C) ⥤ CochainComplex (ModuleCat.{u} C) ℤ :=
  alternatingFaceMapComplex (ModuleCat.{u} C) ⋙
    ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} C)

/-- Unfolding `simplicialModuleToCochain` recovers the extended alternating-face functor. -/
theorem simplicialModuleToCochain_eq :
    simplicialModuleToCochain C =
      alternatingFaceMapComplex (ModuleCat.{u} C) ⋙
        ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} C) :=
  sorry

/-- The cochain-level Jacobi–Zariski sequence of the functorial standard resolutions. -/
def functorialOmegaCochainSequence (h_inj : Function.Injective (algebraMap B C)) :
    ShortComplex (CochainComplex (ModuleCat.{u} C) ℤ) :=
  ShortComplex.mk
    ((simplicialModuleToCochain C).map
      (Functor.whiskerLeft (tripleSimplicial A B C h_inj) (toOmega2 A B C)))
    ((simplicialModuleToCochain C).map
      (Functor.whiskerLeft (tripleSimplicial A B C h_inj) (toOmega3 A B C)))
    sorry

/-- The cochain-level Jacobi–Zariski sequence is short exact. -/
theorem functorialOmegaCochainSequence_shortExact
    (h_inj : Function.Injective (algebraMap B C)) :
    (functorialOmegaCochainSequence A B C h_inj).ShortExact :=
  sorry

/-- Remark 92.7.5 (7): if `B → C` is injective, the distinguished triangle associated to
this short exact sequence of simplicial `C`-modules is the fundamental triangle of
Proposition 92.7.4. -/
@[stacks 08SD]
theorem transitivityTriangle_iso_of_injective
    (h_inj : Function.Injective (algebraMap B C)) :
    IsIsomorphic
      (DerivedCategory.triangleOfSES
        (functorialOmegaCochainSequence_shortExact A B C h_inj))
      (transitivityTriangle A B C) :=
  sorry

/-- The canonical ring map `B → B × C`, `b ↦ (b, algebraMap B C b)`. -/
def prodInclude : B →+* B × C :=
  RingHom.prod (RingHom.id B) (algebraMap B C)

/-- The product algebra `B × C` is an `A`-`B` scalar tower via `Prod.algebra`. -/
instance instIsScalarTower_algebraProd : IsScalarTower A B (B × C) :=
  sorry

/-- Unfolding `prodInclude` recovers `RingHom.prod` of `RingHom.id` and `algebraMap`. -/
theorem prodInclude_eq :
    prodInclude B C = RingHom.prod (RingHom.id B) (algebraMap B C) :=
  sorry

/-- `prodInclude` is the structure map of `Prod.algebra`. -/
theorem prodInclude_eq_algebraMap :
    prodInclude B C = algebraMap B (B × C) :=
  sorry

/-- Remark 92.7.5 (8): the canonical map `B → B × C` is injective, so the previous
construction applies to `A → B → B × C`. -/
@[stacks 08SD]
theorem prodInclude_injective : Function.Injective (prodInclude B C) :=
  sorry

/-- Remark 92.7.5 (9): the projection `B × C → C` is a flat ring map. -/
@[stacks 08SD]
theorem prodToC_flat : (RingHom.snd B C).Flat :=
  sorry

/-- Remark 92.7.5 (10): the product identifications of Lemma 92.6.4, together with
extension of scalars along the flat projection `B × C → C`, induce the fundamental
triangle of `A → B → C` from that of `A → B → B × C`. -/
@[stacks 08SD]
theorem transitivityTriangle_iso_extend_prod :
    IsIsomorphic
      (((ModuleCat.derivedExtensionOfScalars (RingHom.snd B C)).mapTriangle).obj
        (transitivityTriangle A B (B × C)))
      (transitivityTriangle A B C) :=
  sorry
