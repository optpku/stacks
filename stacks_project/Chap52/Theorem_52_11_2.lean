module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.CohomologyStabilization
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

open Scheme Scheme.ModuleDerived.DerivedCompletion

/-- Cohomology of the ordinary direct image of the restriction to `V`, retaining
an ideal argument for compatibility with the degree-zero section construction. -/
noncomputable abbrev neighborhoodCohomology
    {A : Type u} [CommRing A] [IsLocalRing A] (I : Ideal A)
    (M : (scheme A).Modules) (V : (scheme A).Opens) (i : ℕ) : ModuleCat.{u} A :=
  directImageCohomology M V i

/- Theorem 52.11.2: cohomology stabilizes uniformly on sufficiently small neighborhoods
of the closed fiber under the stated vanishing and depth conditions. -/
@[stacks 0DXQ] #check (AlgebraicGeometry.PuncturedSpectrum.existsCohomologyStableNeighborhood :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (h_dualizing : DerivedCategory.HasCanonicalDualizingComplex A)
    (I : Ideal A) [IsAdicComplete I A]
    (F : RingedSpace.Coh (scheme A).toRingedSpace)
    (s d : ℤ)
    (h_cd : ∀ (G : (Spec (CommRingCat.of A)).Modules), G.IsQuasicoherent →
      ∀ q : ℕ, d ≤ (q : ℤ) →
        IsZero (((SheafOfModules.toSheaf (Spec (CommRingCat.of A)).ringCatSheaf).obj G).H'
          q ⟨(PrimeSpectrum.zeroLocus (I : Set A))ᶜ,
            (PrimeSpectrum.isClosed_zeroLocus (I : Set A)).isOpen_compl⟩))
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
                  (ringKrullDim (A ⧸ x.1.asIdeal))),
    ∃ V₀ : (scheme A).Opens,
      (((idealSheafDataOfIdealOnSpec I).comap
        (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V₀ : Set (scheme A)) ∧
      ∀ (V : (scheme A).Opens), V ≤ V₀ →
        (hV : (((idealSheafDataOfIdealOnSpec I).comap
          (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A))) →
          ∀ i : ℕ, (i : ℤ) < s →
            IsIso (openCohomologyComparison I
              ((Scheme.Modules.fromRingedSpace (scheme A)).obj F.obj) V hV i))

/- Theorem 52.11.2 (finiteness): under the additional depth condition on the closed
fiber, the stabilized cohomology groups are finite over the local ring. -/
@[stacks 0DXQ] #check (AlgebraicGeometry.PuncturedSpectrum.existsCohomologyStableFiniteNeighborhood :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (h_dualizing : DerivedCategory.HasCanonicalDualizingComplex A)
    (I : Ideal A) [IsAdicComplete I A]
    (F : RingedSpace.Coh (scheme A).toRingedSpace)
    (s d : ℤ)
    (h_cd : ∀ (G : (Spec (CommRingCat.of A)).Modules), G.IsQuasicoherent →
      ∀ q : ℕ, d ≤ (q : ℤ) →
        IsZero (((SheafOfModules.toSheaf (Spec (CommRingCat.of A)).ringCatSheaf).obj G).H'
          q ⟨(PrimeSpectrum.zeroLocus (I : Set A))ᶜ,
            (PrimeSpectrum.isClosed_zeroLocus (I : Set A)).isOpen_compl⟩))
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
              (ringKrullDim (A ⧸ x.1.asIdeal))),
    ∃ V₀ : (scheme A).Opens,
      (((idealSheafDataOfIdealOnSpec I).comap
        (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V₀ : Set (scheme A)) ∧
      ∀ (V : (scheme A).Opens), V ≤ V₀ →
        (hV : (((idealSheafDataOfIdealOnSpec I).comap
          (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A))) →
          ∀ i : ℕ, (i : ℤ) < s →
            IsIso (openCohomologyComparison I
              ((Scheme.Modules.fromRingedSpace (scheme A)).obj F.obj) V hV i) ∧
            Module.Finite A
              (cohomologyOnOpen
                ((Scheme.Modules.fromRingedSpace (scheme A)).obj F.obj) V i))

end AlgebraicGeometry.PuncturedSpectrum
