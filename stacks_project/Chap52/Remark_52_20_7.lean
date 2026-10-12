/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.PrincipalLocalConditions
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/- Remark 52.20.7: for a Noetherian complete local ring with a dualizing
complex and `f` in its maximal ideal, a coherent formal module on the
punctured spectrum whose completed stalks satisfy module `(S₂)` after
inverting `f` and whose associated-prime quotients have dimension at least
three lies in the essential image of coherent completion. -/
@[stacks 0EJC] #check (AlgebraicGeometry.Scheme.CoherentFormalModules.isCompletion_of_principal_local_conditions :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (S : AffineAlgebraizationSetup A)
    (f : A) [IsAdicComplete (Ideal.span ({f} : Set A)) A]
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
          (3 : WithBot ℕ∞) ≤ ringKrullDim ((completedLocalRing S yU) ⧸ p)),
    (CoherentCompletion.functor
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).essImage F)

end AlgebraicGeometry.Scheme.CoherentFormalModules
