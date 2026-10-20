/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.EtaleNeighborhood
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 41.17.2 (1): Finitely many points of one fibre where a separated scheme
morphism is unramified admit, after an étale base change, a pairwise disjoint clopen
decomposition into closed-immersion branches through the marked point and a complementary part
whose marked fibre avoids the chosen points. -/
@[stacks 04HI] #check
  (AlgebraicGeometry.Scheme.Hom.exists_clopen_decomposition_closedImmersion :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] (s : S) (n : ℕ) (x : Fin n → X)
    (h_image : ∀ i, f (x i) = s) (h_unramified : ∀ i, f.UnramifiedAt (x i)),
    ∃ (U : EtaleNeighborhood S s) (m : Fin n → ℕ)
      (D : Option (Σ i, Fin (m i)) → (pullback f U.toEtale.hom).Opens),
      let P := pullback f U.toEtale.hom
      ∃ (_ : iSup D = ⊤)
        (_ : Pairwise (fun a b ↦ Disjoint (D a : Set P) (D b : Set P)))
        (_ : ∀ a, IsClopen (D a : Set P))
        (_ : ∀ i j,
          let V := D (some ⟨i, j⟩)
          let pV := V.ι ≫ pullback.snd f U.toEtale.hom
          ∃ (_ : IsClosedImmersion pV), U.point ∈ Set.range pV),
        let W := D none
        let pW := W.ι ≫ pullback.snd f U.toEtale.hom
        let qW := W.ι ≫ pullback.fst f U.toEtale.hom
        ∀ w : W, pW w = U.point → ∀ i, qW w ≠ x i)

/- Lemma 41.17.2 (2): If the chosen points exhaust the original fibre, the complementary
clopen part in the étale-local closed-immersion decomposition has empty marked fibre. -/
@[stacks 04HI] #check
  (AlgebraicGeometry.Scheme.Hom.exists_clopen_decomposition_closedImmersion_emptyFiber :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] (s : S) (n : ℕ) (x : Fin n → X)
    (h_image : ∀ i, f (x i) = s) (h_unramified : ∀ i, f.UnramifiedAt (x i))
    (h_fiber : f ⁻¹' ({s} : Set S) = Set.range x),
    ∃ (U : EtaleNeighborhood S s) (m : Fin n → ℕ)
      (D : Option (Σ i, Fin (m i)) → (pullback f U.toEtale.hom).Opens),
      let P := pullback f U.toEtale.hom
      ∃ (_ : iSup D = ⊤)
        (_ : Pairwise (fun a b ↦ Disjoint (D a : Set P) (D b : Set P)))
        (_ : ∀ a, IsClopen (D a : Set P))
        (_ : ∀ i j,
          let V := D (some ⟨i, j⟩)
          let pV := V.ι ≫ pullback.snd f U.toEtale.hom
          ∃ (_ : IsClosedImmersion pV), U.point ∈ Set.range pV),
        let W := D none
        let pW := W.ι ≫ pullback.snd f U.toEtale.hom
        IsEmpty (pW.fiber U.point))

end AlgebraicGeometry.Scheme.Hom
