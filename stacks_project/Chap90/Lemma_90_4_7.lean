module

public import ReasLib.RingTheory.Completion.IdealFiltration
import StacksCheckRecall

/-!
# Maximal-adic topology after quotient by an intersection

In the completed base category, a decreasing family of ideals containing the
maximal-adic powers induces the maximal-adic topology on the quotient by the
intersection.
-/

@[expose] public section

open IsLocalRing

universe u

/- Lemma 90.4.7: objects of the completed base category supply the commutative,
Noetherian, complete local ring hypotheses below. For `I = ⨅ i, J i`, the images
of the decreasing family `J` define the topology given by powers of the image of
`maximalIdeal R`. This image ideal is the quotient maximal ideal whenever `R ⧸ I`
is nontrivial. The mapped-ideal formulation also covers the zero quotient. -/
@[stacks 06SE] #check (IsCompleteLocalRing.definesMaximalAdicTopology_map_iInf :
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
    (J : ℕ → Ideal R), Antitone J → (∀ n, maximalIdeal R ^ n ≤ J n) →
    let I := ⨅ i, J i;
    (∀ n, (maximalIdeal R).map (Ideal.Quotient.mk I) ^ n ≤
        (J n).map (Ideal.Quotient.mk I)) ∧
      ∀ n, ∃ N, (J N).map (Ideal.Quotient.mk I) ≤
        (maximalIdeal R).map (Ideal.Quotient.mk I) ^ n)

#check (IsCompleteLocalRing.definesMaximalAdicTopology_quotient :
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
    (J : ℕ → Ideal R), Antitone J → (∀ n, maximalIdeal R ^ n ≤ J n) →
    ∀ [IsLocalRing (R ⧸ ⨅ i, J i)],
    let I := ⨅ i, J i;
    (∀ n, maximalIdeal (R ⧸ I) ^ n ≤ (J n).map (Ideal.Quotient.mk I)) ∧
      ∀ n, ∃ N, (J N).map (Ideal.Quotient.mk I) ≤ maximalIdeal (R ⧸ I) ^ n)
