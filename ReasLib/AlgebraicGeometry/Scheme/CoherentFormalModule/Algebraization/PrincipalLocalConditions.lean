/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Local
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Intrinsic
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Open

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Set TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- A coherent formal module on the punctured spectrum of an adically complete
local ring algebraizes when its completed stalks satisfy module `(S₂)` after
inverting the principal element and their associated-prime quotients have
dimension at least three. -/
theorem isCompletion_of_principal_local_conditions
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (S : AffineAlgebraizationSetup A)
    (f : A)
    [IsAdicComplete (Ideal.span ({f} : Set A)) A]
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A),
        CategoryTheory.DerivedCategory.IsDualizing K)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_a : S.a = IsLocalRing.maximalIdeal A)
    (h_I : S.I = Ideal.span ({f} : Set A))
    (h_f_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hS2 : ∀ y : S.Y, (hy : S.y y ∈ S.U) →
      topologicalKrullDim (closure ({y} : Set S.Y)) = 1 →
      let yU := closedFiberOpenPoint S y hy
      let fhat :=
        (algebraMap ((S.U.toScheme).presheaf.stalk yU)
          (completedLocalRing S yU)) ((localRingMap S yU) f)
      Module.SerreConditionS (Localization.Away fhat)
        (LocalizedModule.Away fhat (completedStalk S F yU)) 2)
    (hAssDim : ∀ y : S.Y, (hy : S.y y ∈ S.U) →
      topologicalKrullDim (closure ({y} : Set S.Y)) = 1 →
      let yU := closedFiberOpenPoint S y hy
      let fhat :=
        (algebraMap ((S.U.toScheme).presheaf.stalk yU)
          (completedLocalRing S yU)) ((localRingMap S yU) f)
      ∀ p : Ideal (completedLocalRing S yU),
        p ∈ associatedPrimes (completedLocalRing S yU)
          (LocalizedModule.Away fhat (completedStalk S F yU)) →
          (3 : WithBot ℕ∞) ≤ ringKrullDim ((completedLocalRing S yU) ⧸ p)) :
    (CoherentCompletion.functor
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).essImage F := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
