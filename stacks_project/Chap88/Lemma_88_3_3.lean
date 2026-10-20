module

public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.Limit
import StacksCheckRecall

/-!
# Lemma 88.3.3

The ordinary reductions of the completed naive cotangent complex and the stage
naive cotangent complexes are strictly pro-isomorphic. The completed complex
is a homotopy limit of the stage-derived system.
-/

@[expose] public section

open CategoryTheory Algebra.NaiveCotangent.Adic

universe u

variable {A B ι : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B] [Fintype ι]
variable (I : Ideal A) [Algebra.TopologicallyFiniteType I B]
variable (P : Presentation A B I ι)

/- Lemma 88.3.3: complex-level comparison. -/
@[stacks 0AJS] #check (Algebra.NaiveCotangent.Adic.exists_isShiftInverse I P :
    ∃ (c : ℕ) (β : (stageSystem I P).shift c ⟶ modSystem I P),
      Pro.SequentialHom.IsShiftInverse (modToStageNatTrans I P) c β)

/- Lemma 88.3.3: completeness of the ordinary reduction tower. -/
@[stacks 0AJS] #check (Algebra.NaiveCotangent.Adic.naiveCotangentObject_isHomotopyLimit_mod I P :
    HomotopyLimit.IsOf (modDerivedSystem I P) (naiveCotangentObject I P))

/- Lemma 88.3.3 (1): strict isomorphism of the two pro-objects in D(B). -/
@[stacks 0AJS] #check (Algebra.NaiveCotangent.Adic.modToStageDerivedNatTrans_hasShiftInverse I P :
    ∃ (c : ℕ) (β : (stageDerivedSystem I P).shift c ⟶ modDerivedSystem I P),
      Pro.SequentialHom.IsShiftInverse (modToStageDerivedNatTrans I P) c β)

/- Lemma 88.3.3: invertibility of the derived comparison representative. -/
@[stacks 0AJS] #check (Algebra.NaiveCotangent.Adic.modDerivedSystem_hasRepresentativeInverse I P :
    (modToStageDerivedHom I P).HasRepresentativeInverse)

/- Lemma 88.3.3 (2): the completed complex is the derived inverse limit. -/
@[stacks 0AJS] #check (Algebra.NaiveCotangent.Adic.naiveCotangentObject_isHomotopyLimit I P :
    HomotopyLimit.IsOf (stageDerivedSystem I P) (naiveCotangentObject I P))

