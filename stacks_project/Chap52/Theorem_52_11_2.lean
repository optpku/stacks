/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap52.Theorem_52_11_2_Comparison
public import stacks_project.Chap52.Lemma_52_9_5
public import stacks_project.Chap52.Lemma_52_9_3

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

open Scheme Scheme.ModuleDerived.DerivedCompletion

/-- Theorem 52.11.2 (1): let `A` be a Noetherian local ring with a dualizing
complex and let `A` be `I`-adically complete. If `F` is coherent on the punctured
spectrum, `HasDimensionLE I d`, and every point away from `V(I)` whose closure
meets `puncturedOpen A ∩ V(I)` satisfies the stated depth alternative, then some
neighborhood `V₀` of that intersection makes `cohomologyComparison` an isomorphism
for every smaller admissible neighborhood and every `(i : ℤ) < s`. -/
@[stacks 0DXQ]
theorem existsCohomologyStableNeighborhood
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    (I : Ideal A) [IsAdicComplete I A]
    (F : RingedSpace.Coh (scheme A).toRingedSpace)
    (s d : ℤ) (h_cd : Ideal.LocalCohomology.HasDimensionLE I d)
    (h_depth : ∀ x : scheme A,
      x.1 ∉ PrimeSpectrum.zeroLocus (I : Set A) →
        Set.Nonempty
          (closure ({x.1} : Set (PrimeSpectrum A)) ∩
            (({IsLocalRing.closedPoint A} : Set (PrimeSpectrum A))ᶜ ∩
              PrimeSpectrum.zeroLocus (I : Set A))) →
          (s : EInt) ≤
              ((WithTop.map Int.ofNat
                (moduleDepth ((scheme A).presheaf.stalk x)
                  (RingedSpace.stalkModuleCat F.obj x)) : WithTop ℤ) : EInt) ∨
            ((d + s : ℤ) : EInt) <
              ((WithTop.map Int.ofNat
                (moduleDepth ((scheme A).presheaf.stalk x)
                  (RingedSpace.stalkModuleCat F.obj x)) : WithTop ℤ) : EInt) +
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim (A ⧸ x.1.asIdeal))) :
    ∃ V₀ : (scheme A).Opens,
      (((idealSheafDataOfIdealOnSpec I).comap
        (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V₀ : Set (scheme A)) ∧
      ∀ (V : (scheme A).Opens), V ≤ V₀ →
        (hV : (((idealSheafDataOfIdealOnSpec I).comap
          (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A))) →
          ∀ i : ℕ, (i : ℤ) < s →
            IsIso (cohomologyComparison I
              ((Scheme.Modules.fromRingedSpace (scheme A)).obj F.obj) V hV i) := sorry

/-- Theorem 52.11.2 (2): under the hypotheses of part (1), if additionally
`depth(Fₓ) + ringKrullDim (A ⧸ x.asIdeal) > s` on `puncturedOpen A ∩ V(I)`,
the stable neighborhood can be chosen so that the same comparisons are isomorphisms
and all the corresponding cohomology groups are finite `A`-modules. -/
@[stacks 0DXQ]
theorem existsCohomologyStableFiniteNeighborhood
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    (I : Ideal A) [IsAdicComplete I A]
    (F : RingedSpace.Coh (scheme A).toRingedSpace)
    (s d : ℤ) (h_cd : Ideal.LocalCohomology.HasDimensionLE I d)
    (h_depth : ∀ x : scheme A,
      x.1 ∉ PrimeSpectrum.zeroLocus (I : Set A) →
        Set.Nonempty
          (closure ({x.1} : Set (PrimeSpectrum A)) ∩
            (({IsLocalRing.closedPoint A} : Set (PrimeSpectrum A))ᶜ ∩
              PrimeSpectrum.zeroLocus (I : Set A))) →
          (s : EInt) ≤
              ((WithTop.map Int.ofNat
                (moduleDepth ((scheme A).presheaf.stalk x)
                  (RingedSpace.stalkModuleCat F.obj x)) : WithTop ℤ) : EInt) ∨
            ((d + s : ℤ) : EInt) <
              ((WithTop.map Int.ofNat
                (moduleDepth ((scheme A).presheaf.stalk x)
                  (RingedSpace.stalkModuleCat F.obj x)) : WithTop ℤ) : EInt) +
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim (A ⧸ x.1.asIdeal)))
    (h_depth_on_VI : ∀ x : scheme A,
      x.1 ∈ PrimeSpectrum.zeroLocus (I : Set A) →
        (s : EInt) <
          ((WithTop.map Int.ofNat
            (moduleDepth ((scheme A).presheaf.stalk x)
              (RingedSpace.stalkModuleCat F.obj x)) : WithTop ℤ) : EInt) +
            WithBot.map (WithTop.map Int.ofNat)
              (ringKrullDim (A ⧸ x.1.asIdeal))) :
    ∃ V₀ : (scheme A).Opens,
      (((idealSheafDataOfIdealOnSpec I).comap
        (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V₀ : Set (scheme A)) ∧
      ∀ (V : (scheme A).Opens), V ≤ V₀ →
        (hV : (((idealSheafDataOfIdealOnSpec I).comap
          (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A))) →
          ∀ i : ℕ, (i : ℤ) < s →
            IsIso (cohomologyComparison I
              ((Scheme.Modules.fromRingedSpace (scheme A)).obj F.obj) V hV i) ∧
            Module.Finite A
              (neighborhoodCohomology I
                ((Scheme.Modules.fromRingedSpace (scheme A)).obj F.obj) V i) := sorry

end AlgebraicGeometry.PuncturedSpectrum
