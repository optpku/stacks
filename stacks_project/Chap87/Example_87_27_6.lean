/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalSpectrum.WeakIdealCompletion.Quotient
public import ReasLib.RingTheory.Topology.WeakIdealCompletion.Quotient

/-!
# Example 87.27.6

For a weakly admissible ring `A` over `S` and a closed ideal `K`, the completion
`B = (A ⧸ K)^∧` is the inverse limit of `A ⧸ (I.ideal ⊔ K)` over weak ideals
of definition `I`. The canonical morphism `Spf(B) ⟶ Spf(A)` is representable.
A quasi-compact scheme `T ⟶ Spf(A)` factors through some `Spec(A ⧸ I.ideal)`;
its fibre product with `Spf(B)` is then
`T ×_{Spec(A ⧸ I.ideal)} Spec(A ⧸ (I.ideal ⊔ K))`.
This yields a closed immersion, although the canonical ring map need not be
surjective. Its kernel is exactly `K`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalRing
open AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.FormalAlgebraicSpace

noncomputable section

universe u

section Geometry

variable {S : Scheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
  [IsWeaklyAdmissibleRing A] (hA : Spec (.of A) ⟶ S)
  [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] (K : Ideal A)

section ClosedIdeal

variable [IsClosed (K : Set A)]

/- Example 87.27.6 (1): The canonical morphism `Spf((A ⧸ K)^∧) ⟶ Spf(A)`
is a closed immersion. -/
@[stacks 0ANR] #check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.instClosedImmersion_spfMap_weakIdealCompletion_quotient
    hA K : ClosedImmersion
      ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
        (spfMap_weakIdealCompletion hA (A ⧸ K))))

end ClosedIdeal

#check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.representableByAlgebraicSpaces_spfMap_weakIdealCompletion
    hA (A ⧸ K) : AlgebraicSpace.representableByAlgebraicSpaces
      ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
        (spfMap_weakIdealCompletion hA (A ⧸ K))))

variable (I : WeakIdealOfDefinition A)

#check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.isPullback_stage_spfMap_weakIdealCompletion_quotient
    hA K I :
    IsPullback (yoneda.map (specQuotSupHom hA K I)) (specQuotSupStageι hA K I)
      (spfStageι hA I)
      ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
        (spfMap_weakIdealCompletion hA (A ⧸ K))))

variable {T : Over S} [CompactSpace T.left]
  (ξ : yoneda.obj T ⟶ (spf A hA).obj)

#check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.exists_factorThroughStage_spf hA ξ :
    ∃ (J : WeakIdealOfDefinition A) (g : yoneda.obj T ⟶ yoneda.obj (stage A hA J)),
      g ≫ spfStageι hA J = ξ)

variable (g : yoneda.obj T ⟶ yoneda.obj (stage A hA I))
  {P : (Over S)ᵒᵖ ⥤ Type u} (fst : P ⟶ yoneda.obj T)
  (snd : P ⟶ yoneda.obj (specQuotSupStage hA K I))
  (hp : IsPullback fst snd g (yoneda.map (specQuotSupHom hA K I)))

#check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.isPullback_spfMap_weakIdealCompletion_quotient_of_factor
    hA K g fst snd hp :
    IsPullback fst (snd ≫ specQuotSupStageι hA K I) (g ≫ spfStageι hA I)
      ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
        (spfMap_weakIdealCompletion hA (A ⧸ K))))

end Geometry

section Kernel

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A]
  (K : Ideal A) [IsClosed (K : Set A)]

/- Example 87.27.6 (2): The kernel of the canonical map `A → (A ⧸ K)^∧`
is the closed ideal `K`. -/
@[stacks 0ANR] #check
  (TopologicalRing.weakIdealCompletion.ker_algebraMap_quotient K :
    RingHom.ker (algebraMap A (weakIdealCompletion A (A ⧸ K))) = K)

end Kernel

/- Example 87.27.6 (3): The canonical map into the completion of a closed
quotient need not be surjective. -/
@[stacks 0ANR] #check
  (TopologicalRing.weakIdealCompletion.exists_not_surjective_algebraMap_quotient :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : IsWeaklyAdmissibleRing A) (K : Ideal A),
      IsClosed (K : Set A) ∧
        ¬ Function.Surjective (algebraMap A (weakIdealCompletion A (A ⧸ K))))
