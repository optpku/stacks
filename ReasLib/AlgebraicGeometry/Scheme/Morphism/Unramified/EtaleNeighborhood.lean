/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.EtaleNeighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Local
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Finite

/-!
# Étale-local structure of unramified morphisms
-/

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Finitely many distinct points of one fibre where a scheme morphism is unramified admit,
after an étale base neighbourhood, finite families of open pieces mapping to the neighbourhood
as closed immersions through its marked point, pairwise separated over that point, and covering
all lifted points above the chosen source points. -/
theorem exists_closedImmersionOpen_etaleNeighborhoods
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (n : ℕ) (x : Fin n → X)
    (h_image : ∀ i, f (x i) = s) (h_injective : Function.Injective x)
    (h_unramified : ∀ i, f.UnramifiedAt (x i)) :
    ∃ (U : EtaleNeighborhood S s) (m : Fin n → ℕ)
      (V : ∀ i, Fin (m i) → (pullback f U.toEtale.hom).Opens),
      let P := pullback f U.toEtale.hom
      let p := pullback.snd f U.toEtale.hom
      let q := pullback.fst f U.toEtale.hom
      let pV := fun i j ↦ (V i j).ι ≫ p
      ∃ (h_closed : ∀ i j, IsClosedImmersion (pV i j))
        (h_through : ∀ i j, U.point ∈ Set.range (pV i j))
        (h_separate : ∀ a b : Σ i, Fin (m i),
          U.point ∈ Set.range ((V a.1 a.2 ⊓ V b.1 b.2).ι ≫ p) → a = b),
        ∀ i (w : P), p w = U.point → q w = x i → ∃ j, w ∈ V i j := sorry

/-- Finitely many points of one fibre where a separated scheme morphism is unramified admit,
after an étale base change, a pairwise disjoint clopen decomposition into closed-immersion
branches through the marked point and a complementary part whose marked fibre avoids the
chosen points. -/
theorem exists_clopen_decomposition_closedImmersion
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] (s : S) (n : ℕ) (x : Fin n → X)
    (h_image : ∀ i, f (x i) = s) (h_unramified : ∀ i, f.UnramifiedAt (x i)) :
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
        ∀ w : W, pW w = U.point → ∀ i, qW w ≠ x i := sorry

/-- If finitely many unramified points exhaust a fibre of a separated scheme morphism, then
after an étale base change there is a pairwise disjoint clopen decomposition into
closed-immersion branches through the marked point whose complementary part has empty marked
fibre. -/
theorem exists_clopen_decomposition_closedImmersion_emptyFiber
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] (s : S) (n : ℕ) (x : Fin n → X)
    (h_image : ∀ i, f (x i) = s) (h_unramified : ∀ i, f.UnramifiedAt (x i))
    (h_fiber : f ⁻¹' ({s} : Set S) = Set.range x) :
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
        IsEmpty (pW.fiber U.point) := sorry

/-- A finite unramified morphism becomes, after an étale base change, a finite pairwise
disjoint clopen decomposition whose pieces map to the neighbourhood by closed immersions. -/
theorem exists_clopen_decomposition_closedImmersion_of_finite
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Unramified f] (s : S) :
    ∃ (U : EtaleNeighborhood S s) (n : ℕ),
      let P := pullback f U.toEtale.hom
      let p := pullback.snd f U.toEtale.hom
      ∃ (V : Fin n → P.Opens)
        (_ : iSup V = ⊤)
        (_ : Pairwise (fun i j ↦ Disjoint (V i : Set P) (V j : Set P)))
        (_ : ∀ i, IsClopen (V i : Set P)),
        ∀ i, IsClosedImmersion ((V i).ι ≫ p) := sorry

end AlgebraicGeometry.Scheme.Hom
