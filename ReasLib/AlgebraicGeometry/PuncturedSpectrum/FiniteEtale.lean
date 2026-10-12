/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale
public import Mathlib.RingTheory.Etale.Finite
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.RingTheory.Depth
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.PrincipalQuotient
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.RingTheory.Henselian

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry ENat

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a Noetherian local ring of depth at least two, a finite étale cover of
the punctured spectrum extends over the spectrum exactly when its global-sections
algebra is finite étale. -/
theorem finiteEtale_punctured_iff_globalSections
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (V : Scheme.FiniteEtale (PuncturedSpectrum.scheme A))
    (hdepth : (2 : ℕ∞) ≤ moduleDepth A A) :
    let X : Scheme := Spec (CommRingCat.of A)
    let U : X.Opens := PuncturedSpectrum.puncturedOpen A
    let B : CommAlgCat A := Scheme.Hom.globalSectionsAlg (V.hom ≫ U.ι)
    (∃ Y : Scheme.FiniteEtale X,
        Nonempty ((Scheme.finiteEtaleBaseChange U.ι).obj Y ≅ V)) ↔
      CommAlgCat.finiteEtale A B := sorry

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.PuncturedSpectrum

open IsLocalRing

noncomputable section

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
variable (f : maximalIdeal A)

/-- For a Noetherian local ring `A` and `f` in its maximal ideal, restriction of
finite étale covers along `principalQuotientMap f` is full if `(A, (f))` is a
henselian pair and powers of `f` annihilate `H¹_𝔪(A)` and `H²_𝔪(A)`. -/
instance finiteEtaleBaseChange_full_of_localCohomology
    [HenselianRing A (principalIdeal f)]
    [Fact (Module.IsAnnihilatedByPower (Ideal.span ({(f : A)} : Set A))
      ((localCohomology (maximalIdeal A) 1).obj (ModuleCat.of A A)))]
    [Fact (Module.IsAnnihilatedByPower (Ideal.span ({(f : A)} : Set A))
      ((localCohomology (maximalIdeal A) 2).obj (ModuleCat.of A A)))] :
    (Scheme.finiteEtaleBaseChange (principalQuotientMap f)).Full := sorry

/-- For a Noetherian local ring `A` and `f` in its maximal ideal, restriction of
finite étale covers along `principalQuotientMap f` is faithful if `(A, (f))` is a
henselian pair and powers of `f` annihilate `H¹_𝔪(A)` and `H²_𝔪(A)`. -/
instance finiteEtaleBaseChange_faithful_of_localCohomology
    [HenselianRing A (principalIdeal f)]
    [Fact (Module.IsAnnihilatedByPower (Ideal.span ({(f : A)} : Set A))
      ((localCohomology (maximalIdeal A) 1).obj (ModuleCat.of A A)))]
    [Fact (Module.IsAnnihilatedByPower (Ideal.span ({(f : A)} : Set A))
      ((localCohomology (maximalIdeal A) 2).obj (ModuleCat.of A A)))] :
    (Scheme.finiteEtaleBaseChange (principalQuotientMap f)).Faithful := sorry

end

end AlgebraicGeometry.PuncturedSpectrum
