module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.CohomologyComparison
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.CanonicalExistence
public import ReasLib.RingTheory.Depth
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Order.WithBotTop
public import Mathlib.RingTheory.AdicCompletion.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

open Scheme Scheme.ModuleDerived.DerivedCompletion

/-- For a coherent sheaf on the punctured spectrum of an adically complete
Noetherian local ring admitting a dualizing complex, cohomological vanishing off
the ideal support and the stalk-depth alternative imply uniform stabilization of
cohomology on sufficiently small neighborhoods below degree `s`. -/
theorem existsCohomologyStableNeighborhood
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
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
                  (ringKrullDim (A ⧸ x.1.asIdeal))) :
    ∃ V₀ : (scheme A).Opens,
      (((idealSheafDataOfIdealOnSpec I).comap
        (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V₀ : Set (scheme A)) ∧
      ∀ (V : (scheme A).Opens), V ≤ V₀ →
        (hV : (((idealSheafDataOfIdealOnSpec I).comap
          (puncturedOpen A).ι).support : Set (scheme A)) ⊆ (V : Set (scheme A))) →
          ∀ i : ℕ, (i : ℤ) < s →
            IsIso (openCohomologyComparison I
              ((Scheme.Modules.fromRingedSpace (scheme A)).obj F.obj) V hV i) := sorry

/-- Under cohomological vanishing and the stalk-depth alternative on a punctured
spectrum, an additional strict depth-plus-dimension bound along the ideal support
makes the stabilized neighborhood cohomology finite over the base ring. -/
theorem existsCohomologyStableFiniteNeighborhood
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
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
              (ringKrullDim (A ⧸ x.1.asIdeal))) :
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
                ((Scheme.Modules.fromRingedSpace (scheme A)).obj F.obj) V i) := sorry

end AlgebraicGeometry.PuncturedSpectrum
