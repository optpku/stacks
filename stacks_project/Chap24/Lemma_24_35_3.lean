/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.ProIsomorphism
public import ReasLib.RingTheory.Sequence.Koszul.Power
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

noncomputable section

universe u v

/-- A finite sequence reindexed into the coefficient ring's universe. -/
private abbrev liftFinSequence {R : Type u} {r : ℕ} (f : Fin r → R) :
    ULift.{u} (Fin r) → R :=
  fun i ↦ f i.down

section PoweredKoszul

variable {R : Type u} [CommRing R]
variable {r : ℕ} (f : Fin r → R)

/- Lemma 24.35.3 (tag 0GZJ), concrete coefficient system: powered Koszul complexes, their
multiplication, and their transitions form the canonical integer-graded cochain-DGA tower used by
the derived module-system API. -/
@[stacks 0GZJ "powered Koszul cochain-DGA inverse system"]
#check
  (KoszulComplex.powerDGASystem (liftFinSequence f) :
    ℕᵒᵖ ⥤ CochainDGAlgebra R)

/- Forgetting multiplication recovers the underlying powered Koszul chain tower. -/
#check
  (KoszulComplex.powerAlgebraSystem_comp_forget (liftFinSequence f) :
    KoszulComplex.powerAlgebraSystem (liftFinSequence f) ⋙
        CommMon.forget (ChainComplex (ModuleCat R) ℕ) =
      KoszulComplex.powerSystem (liftFinSequence f))

/- For exponents `n ≤ m`, the transition is multiplicative and makes `K_n` a canonical
`(K_m, K_n)`-bimodule. -/
#check
  (KoszulComplex.powAlgebraMap (liftFinSequence f) : ∀ {n m : ℕ} (h : n ≤ m),
    KoszulComplex.powAlgebra (liftFinSequence f) m ⟶
      KoszulComplex.powAlgebra (liftFinSequence f) n)

#check
  (KoszulComplex.powBimodule (liftFinSequence f) : ∀ {n m : ℕ} (h : n ≤ m),
    Bimod (KoszulComplex.powAlgebra (liftFinSequence f) m).toMon
      (KoszulComplex.powAlgebra (liftFinSequence f) n).toMon)

/- This is the explicit multiplication map `K_m ⊗ K_n ⟶ K_n` used to compare the two tensor
towers in the source proof. Extension along `ComplexShape.embeddingDownNat` is already strong
monoidal; the remaining bridge is from the resulting cochain `CommMon` objects to the existing
elementwise DG-module derived-tensor API, followed by the varying-algebra diagram and its
divided-power representative inverse. -/
#check
  (KoszulComplex.powTensorMul (liftFinSequence f) : ∀ {n m : ℕ} (h : n ≤ m),
    HomologicalComplex.tensorObj (KoszulComplex.powComplex (liftFinSequence f) m)
        (KoszulComplex.powComplex (liftFinSequence f) n) ⟶
      KoszulComplex.powComplex (liftFinSequence f) n)

end PoweredKoszul

namespace CategoryTheory.IsDerivedLimit

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D]
variable [HasShift D ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor D n)]
variable [Pretriangulated D] [IsTriangulated D]
variable {Ksys Msys : SequentialInverseSystem D} {K M : D}
variable (hK : IsDerivedLimit Ksys K) (hM : IsDerivedLimit Msys M)
variable (η : (Pro.lim (C := D) ℕᵒᵖ).obj Ksys ⟶
  (Pro.lim (C := D) ℕᵒᵖ).obj Msys) [IsIso η]

/- Once the Koszul tensor comparison supplies a pro-isomorphism, this is the exact
presentation-independent derived-limit endpoint. -/
#check
  (existsIso_of_proIso hK hM η :
    ∃ g : K ⟶ M, IsIso g)

end

end CategoryTheory.IsDerivedLimit
