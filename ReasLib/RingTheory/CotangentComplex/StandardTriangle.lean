module

public import ReasLib.Algebra.PolynomialTower.StandardResolution
public import ReasLib.Algebra.PolynomialTower.Differentials
public import ReasLib.AlgebraicTopology.SimplicialObject.ModuleCochain
public import ReasLib.RingTheory.RingHom.Product
public import ReasLib.RingTheory.CotangentComplex.Transitivity
public import ReasLib.RingTheory.CotangentComplex.Product
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# The transitivity triangle from standard polynomial resolutions

The differential sequence of functorial standard polynomial squares gives the
cotangent transitivity triangle. Extension along a product projection gives
the reduction from an arbitrary tower map to an injective one.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Algebra.PolynomialSite HomologicalComplex AlgebraicTopology

noncomputable section

universe u

namespace Algebra.CotangentComplex

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- The simplicial `C`-module `Ω_{P_• / A} ⊗_{P_•} C`. -/
def omegaPSimplicial (h_inj : Function.Injective (algebraMap B C)) :
    SimplicialObject (ModuleCat.{u} C) :=
  tripleSimplicial A B C h_inj ⋙ Algebra.PolynomialTower.tensorOmega1 A B C

/-- Degreewise, `omegaPSimplicial` evaluates `tensorOmega1` on the functorial triple. -/
theorem omegaPSimplicial_obj (h_inj : Function.Injective (algebraMap B C))
    (n : SimplexCategoryᵒᵖ) :
    (omegaPSimplicial A B C h_inj).obj n =
      (Algebra.PolynomialTower.tensorOmega1 A B C).obj (triple A B C n h_inj) := rfl

/-- The simplicial `C`-module `Ω_{Q_• / A} ⊗_{Q_•} C`. -/
def omegaQSimplicial (h_inj : Function.Injective (algebraMap B C)) :
    SimplicialObject (ModuleCat.{u} C) :=
  tripleSimplicial A B C h_inj ⋙ Algebra.PolynomialTower.inverseImageOmega2 A B C

/-- Degreewise, `omegaQSimplicial` evaluates `inverseImageOmega2` on the functorial
triple. -/
theorem omegaQSimplicial_obj (h_inj : Function.Injective (algebraMap B C))
    (n : SimplexCategoryᵒᵖ) :
    (omegaQSimplicial A B C h_inj).obj n =
      (Algebra.PolynomialTower.inverseImageOmega2 A B C).obj (triple A B C n h_inj) := rfl

/-- The simplicial `C`-module `Ω_{Q̄_• / B} ⊗_{Q̄_•} C`. -/
def omegaBarQSimplicial (h_inj : Function.Injective (algebraMap B C)) :
    SimplicialObject (ModuleCat.{u} C) :=
  tripleSimplicial A B C h_inj ⋙ Algebra.PolynomialTower.inverseImageOmega3 A B C

/-- Degreewise, `omegaBarQSimplicial` evaluates `inverseImageOmega3` on the functorial
triple. -/
theorem omegaBarQSimplicial_obj (h_inj : Function.Injective (algebraMap B C))
    (n : SimplexCategoryᵒᵖ) :
    (omegaBarQSimplicial A B C h_inj).obj n =
      (Algebra.PolynomialTower.inverseImageOmega3 A B C).obj (triple A B C n h_inj) := rfl

/-- The cochain complex of `C`-modules associated to `Ω_{Q̄_• / B} ⊗_{Q̄_•} C`. -/
def omegaBarQCochain (h_inj : Function.Injective (algebraMap B C)) :
    CochainComplex (ModuleCat.{u} C) ℤ :=
  ((alternatingFaceMapComplex (ModuleCat.{u} C)).obj
      (omegaBarQSimplicial A B C h_inj)).extend ComplexShape.embeddingDownNat


/-- The relative differential complex of the tensor resolution represents the relative cotangent complex. -/
theorem barQ_represents_relative (h_inj : Function.Injective (algebraMap B C)) :
    IsIsomorphic (derived B C)
      (DerivedCategory.Q.obj (omegaBarQCochain A B C h_inj)) :=
  sorry

/-- The cochain-level Jacobi–Zariski sequence of the functorial standard resolutions. -/
def functorialOmegaCochainSequence (h_inj : Function.Injective (algebraMap B C)) :
    ShortComplex (CochainComplex (ModuleCat.{u} C) ℤ) :=
  (((Algebra.PolynomialTower.omegaSequence A B C).map
    ((Functor.whiskeringLeft _ _ _).obj (tripleSimplicial A B C h_inj))).map
      (alternatingFaceMapComplex (ModuleCat.{u} C))).map
        (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} C))

/-- The cochain-level Jacobi–Zariski sequence is short exact. -/
theorem functorialOmegaCochainSequence_shortExact
    (h_inj : Function.Injective (algebraMap B C)) :
    (functorialOmegaCochainSequence A B C h_inj).ShortExact :=
  sorry

/-- For an injective tower map, the differential short exact sequence gives the transitivity triangle. -/
theorem transitivityTriangle_iso_of_injective
    (h_inj : Function.Injective (algebraMap B C)) :
    IsIsomorphic
      (DerivedCategory.triangleOfSES
        (functorialOmegaCochainSequence_shortExact A B C h_inj))
      (transitivityTriangle A B C) :=
  sorry

/-- Extension along the second product projection identifies the product tower's transitivity triangle with that of the original tower. -/
theorem transitivityTriangle_iso_extend_prod :
    IsIsomorphic
      (((ModuleCat.derivedExtensionOfScalars (RingHom.snd B C)).mapTriangle).obj
        (transitivityTriangle A B (B × C)))
      (transitivityTriangle A B C) :=
  sorry

end Algebra.CotangentComplex
