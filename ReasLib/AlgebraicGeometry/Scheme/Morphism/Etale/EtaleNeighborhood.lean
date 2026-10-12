/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.EtaleNeighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.OpenImmersion

/-!
# Étale-local structure of étale morphisms
-/

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Finitely many distinct points of one fibre at which a scheme morphism is étale admit,
after an étale base neighbourhood, finite families of open branches mapping isomorphically to
the neighbourhood, pairwise separated over its marked point, and covering all lifted points
above the chosen source points. -/
@[stacks 04HL]
theorem exists_isIsoOpen_etaleNeighborhoods
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (n : ℕ) (x : Fin n → X)
    (h_image : ∀ i, f (x i) = s) (h_injective : Function.Injective x)
    (h_etale : ∀ i, f.EtaleAt (x i)) :
    ∃ (U : EtaleNeighborhood S s) (m : Fin n → ℕ)
      (V : ∀ i, Fin (m i) → (pullback f U.toEtale.hom).Opens),
      let P := pullback f U.toEtale.hom
      let p := pullback.snd f U.toEtale.hom
      let q := pullback.fst f U.toEtale.hom
      let pV := fun i j ↦ (V i j).ι ≫ p
      ∃ (h_iso : ∀ i j, IsIso (pV i j))
        (h_separate : ∀ a b : Σ i, Fin (m i),
          U.point ∈ Set.range ((V a.1 a.2 ⊓ V b.1 b.2).ι ≫ p) → a = b),
        ∀ i (w : P), p w = U.point → q w = x i → ∃ j, w ∈ V i j := sorry

/-- Finitely many points of one fibre where a separated scheme morphism is étale admit,
after an étale base change, a pairwise disjoint clopen decomposition into branches
isomorphic to the base neighbourhood and a complementary part whose marked fibre avoids the
chosen points. -/
@[stacks 04HM]
theorem exists_clopen_decomposition_isIso
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] (s : S) (n : ℕ) (x : Fin n → X)
    (h_image : ∀ i, f (x i) = s) (h_etale : ∀ i, f.EtaleAt (x i)) :
    ∃ (U : EtaleNeighborhood S s) (m : Fin n → ℕ)
      (D : Option (Σ i, Fin (m i)) → (pullback f U.toEtale.hom).Opens),
      let P := pullback f U.toEtale.hom
      ∃ (_ : iSup D = ⊤)
        (_ : Pairwise (fun a b ↦ Disjoint (D a : Set P) (D b : Set P)))
        (_ : ∀ a, IsClopen (D a : Set P))
        (_ : ∀ i j,
          let V := D (some ⟨i, j⟩)
          let pV := V.ι ≫ pullback.snd f U.toEtale.hom
          IsIso pV),
        let W := D none
        let pW := W.ι ≫ pullback.snd f U.toEtale.hom
        let qW := W.ι ≫ pullback.fst f U.toEtale.hom
        ∀ w : W, pW w = U.point → ∀ i, qW w ≠ x i := sorry

/-- If finitely many points exhaust a fibre of a separated scheme morphism that is étale at
those points, then after an étale base change the complementary clopen part in the local
decomposition into isomorphic branches has empty marked fibre. -/
@[stacks 04HM]
theorem exists_clopen_decomposition_isIso_emptyFiber
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] (s : S) (n : ℕ) (x : Fin n → X)
    (h_image : ∀ i, f (x i) = s) (h_etale : ∀ i, f.EtaleAt (x i))
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
          IsIso pV),
        let W := D none
        let pW := W.ι ≫ pullback.snd f U.toEtale.hom
        IsEmpty (pW.fiber U.point) := sorry

end AlgebraicGeometry.Scheme.Hom
