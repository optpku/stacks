/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Blowup
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 38.30.6: finite compatible étale covers carrying admissible blowups that flatten the
local strict transforms yield a `U`-admissible blowup that flattens the global strict transform. -/
@[stacks 0814] #check
  (AlgebraicGeometry.Scheme.Modules.exists_isAdmissibleBlowup_flattening_of_etaleCover :
    ∀ {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
      (f : X ⟶ S) (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      (U : S.Opens) [QuasiCompact U.ι] {n : ℕ}
      (Sᵢ Xᵢ Sᵢ' : Fin n → Scheme.{u})
      (eᵢ : ∀ i, Sᵢ i ⟶ S) (jᵢ : ∀ i, Xᵢ i ⟶ X)
      (fᵢ : ∀ i, Xᵢ i ⟶ Sᵢ i) (bᵢ : ∀ i, Sᵢ' i ⟶ Sᵢ i)
      (Iᵢ : ∀ i, (Sᵢ i).IdealSheafData)
      [∀ i, QuasiCompact (eᵢ i)] [∀ i, Etale (eᵢ i)] [∀ i, Etale (jᵢ i)]
      (sq : ∀ i, CommSq (jᵢ i) (fᵢ i) f (eᵢ i))
      (hS : ∀ s : S, ∃ i, s ∈ Set.range (eᵢ i))
      (hX : ∀ x : X, ∃ i, x ∈ Set.range (jᵢ i))
      [∀ i, IsAdmissibleBlowupCenter ((eᵢ i) ⁻¹ᵁ U) (bᵢ i) (Iᵢ i)]
      (hflat : ∀ i, AlgebraicGeometry.Scheme.Modules.flatOver
        (AlgebraicGeometry.strictTransformModule (bᵢ i) ((Iᵢ i).comap (bᵢ i)) (fᵢ i)
          ((Scheme.Modules.pullback (jᵢ i)).obj ℱ))
        (pullback.snd (fᵢ i) (bᵢ i))),
      ∃ (S' : Scheme.{u}) (b : S' ⟶ S) (I : S.IdealSheafData),
        IsAdmissibleBlowupCenter U b I ∧
          AlgebraicGeometry.Scheme.Modules.flatOver
            (AlgebraicGeometry.strictTransformModule b (I.comap b) f ℱ) (pullback.snd f b))
