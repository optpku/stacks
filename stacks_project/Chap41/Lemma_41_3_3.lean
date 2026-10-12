/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.LocalMap.Unramified
public import ReasLib.RingTheory.Unramified.DiscreteValuationRing
import StacksCheckRecall

@[expose] public section

open Ideal IsLocalRing

universe u v

/- Lemma 41.3.3 (1): an unramified local homomorphism of Noetherian local rings induces a
finite module on their maximal-ideal completions. -/
@[stacks 039H]
#check
  (AdicCompletion.LocalMap.finite_of_formallyUnramified :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
      [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
      [Algebra.FormallyUnramified A B],
      @Module.Finite
        (AdicCompletion (maximalIdeal A) A)
        (AdicCompletion (maximalIdeal B) B)
        inferInstance inferInstance
        (AdicCompletion.mapLocalAlgebra (algebraMap A B)).toModule)

/- Lemma 41.3.3 (2): if the residue-field map of an unramified local homomorphism of
Noetherian local rings is bijective, then the induced map on maximal-ideal completions is
surjective. -/
@[stacks 039H]
#check
  (AdicCompletion.LocalMap.surjective_of_formallyUnramified_of_residueField_bijective :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
      [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
      [Algebra.FormallyUnramified A B],
      Function.Bijective (ResidueField.map (algebraMap A B)) →
        Function.Surjective (AdicCompletion.mapLocal (algebraMap A B)))

/- Lemma 41.3.3 (3): if the source residue field is separably closed, then an unramified local
homomorphism of Noetherian local rings induces a surjection on maximal-ideal completions. -/
@[stacks 039H]
#check
  (AdicCompletion.LocalMap.surjective_of_formallyUnramified_of_isSepClosed :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
      [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
      [Algebra.FormallyUnramified A B] [IsSepClosed (ResidueField A)],
      Function.Surjective (AdicCompletion.mapLocal (algebraMap A B)))

/- Lemma 41.3.3 (4): for complete discrete valuation rings, being formally unramified and
essentially of finite type is equivalent to a chosen source uniformizer mapping to a target
uniformizer together with a finite separable residue-field extension and essential finite type. -/
@[stacks 039H]
#check
  (Algebra.FormallyUnramified.iff_uniformizer_and_residueField :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalHom (algebraMap A B)]
      [IsAdicComplete (maximalIdeal A) A] [IsAdicComplete (maximalIdeal B) B]
      (π : A), maximalIdeal A = Ideal.span ({π} : Set A) →
        ((Algebra.FormallyUnramified A B ∧ Algebra.EssFiniteType A B) ↔
          maximalIdeal B = Ideal.span ({algebraMap A B π} : Set B) ∧
          FiniteDimensional (ResidueField A) (ResidueField B) ∧
          Algebra.IsSeparable (ResidueField A) (ResidueField B) ∧
          Algebra.EssFiniteType A B))

end
