/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.CanonicalExistence
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension
public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Serre
public import Mathlib.Order.WithBotTop
public import Mathlib.RingTheory.AdicCompletion.Basic

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
open scoped ENat
open AlgebraicGeometry.Scheme.Opens

noncomputable section

universe u

namespace AlgebraicGeometry.AffineAlgebraizationSetup

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- For nested ideals in a Noetherian ring complete along the smaller ideal and admitting a
canonical dualizing complex, a coherent module on the complement of the larger ideal has
bijective formal-section comparison if its associated-point closures satisfy the strict local
dimension bound and either its restriction off the smaller ideal satisfies `(S₁)` or the larger
ideal has quotient ring of Krull dimension at most two. -/
theorem neighborhoodComparison_bijective_of_associatedPointDimension
    (S : AffineAlgebraizationSetup A)
    (h_dualizing : DerivedCategory.HasCanonicalDualizingComplex A)
    [IsAdicComplete S.I A]
    (F : RingedSpace.Coh (S.U.toScheme).toRingedSpace)
    (h_dimension : ∀ x : S.U, x ∈ associatedPoints F.obj →
      S.U.ι x ∉ (idealSheafDataOfIdealOnSpec S.I).support →
        ¬ Set.range (PointClosure.ι (S.U.ι x)) ∩
            (idealSheafDataOfIdealOnSpec S.I).support ⊆ S.U.compl →
          ∀ z : PointClosure.scheme (S.U.ι x),
            PointClosure.ι (S.U.ι x) z ∈ S.U.compl →
              ((Ideal.LocalCohomology.dimension S.I
                  S.I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim
                    ((PointClosure.scheme (S.U.ι x)).presheaf.stalk z)))
    (h_alternative :
      coherentSatisfiesSerreConditionS
        ((coherentRestrictFunctor
          (idealOnOpen S).openComplement.ι).obj F) 1 ∨
        ringKrullDim (A ⧸ S.a) ≤ 2) :
    Function.Bijective (globalNeighborhoodComparison S F.obj) := sorry

/-- For nested ideals in a Noetherian ring complete along the smaller ideal and admitting a
canonical dualizing complex, the formal global-section comparison is bijective when the
associated-point closures satisfy the strict local dimension bound. -/
theorem globalNeighborhoodComparison_bijective_of_associatedPointDimension
    (S : AffineAlgebraizationSetup A)
    (h_dualizing : DerivedCategory.HasCanonicalDualizingComplex A)
    [IsAdicComplete S.I A]
    (F : RingedSpace.Coh (S.U.toScheme).toRingedSpace)
    (h_dimension : ∀ x : S.U, x ∈ associatedPoints F.obj →
      S.U.ι x ∉ (idealSheafDataOfIdealOnSpec S.I).support →
        ¬ Set.range (PointClosure.ι (S.U.ι x)) ∩
            (idealSheafDataOfIdealOnSpec S.I).support ⊆ S.U.compl →
          ∀ z : PointClosure.scheme (S.U.ι x),
            PointClosure.ι (S.U.ι x) z ∈ S.U.compl →
              ((Ideal.LocalCohomology.dimension S.I
                  S.I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim
                    ((PointClosure.scheme (S.U.ι x)).presheaf.stalk z))) :
    Function.Bijective (globalNeighborhoodComparison S F.obj) := sorry

/-- For nested ideals in a Noetherian ring complete along the smaller ideal and admitting a
canonical dualizing complex, the canonical comparison from global sections of a coherent module
to the inverse limit of its positive-power quotient sections is bijective if the associated-point
closures outside the smaller ideal that meet its vanishing locus outside the larger ideal satisfy
the strict local dimension bound, and every point whose closure meets the smaller ideal's
vanishing locus only inside the larger ideal's vanishing locus has stalk depth at least two. -/
theorem sectionsComparison_bijective_of_associatedPointDimension
    (S : AffineAlgebraizationSetup A)
    (h_dualizing : DerivedCategory.HasCanonicalDualizingComplex A)
    [IsAdicComplete S.I A]
    (F : RingedSpace.Coh (S.U.toScheme).toRingedSpace)
    (h_dimension : ∀ x : S.U, x ∈ associatedPoints F.obj →
      S.U.ι x ∉ (idealSheafDataOfIdealOnSpec S.I).support →
        ¬ Set.range (PointClosure.ι (S.U.ι x)) ∩
            (idealSheafDataOfIdealOnSpec S.I).support ⊆ S.U.compl →
          ∀ z : PointClosure.scheme (S.U.ι x),
            PointClosure.ι (S.U.ι x) z ∈ S.U.compl →
              ((Ideal.LocalCohomology.dimension S.I
                  S.I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim
                    ((PointClosure.scheme (S.U.ι x)).presheaf.stalk z)))
    (h_depth : ∀ x : S.U,
      Set.range (PointClosure.ι (S.U.ι x)) ∩
          (idealSheafDataOfIdealOnSpec S.I).support ⊆ S.U.compl →
        (2 : ℕ∞) ≤ moduleDepth ((S.U.toScheme).presheaf.stalk x)
          (RingedSpace.stalkModuleCat F.obj x)) :
    Function.Bijective
      (Scheme.CoherentCompletion.sectionsComparison (idealOnOpen S) F.obj) := sorry

/-- For nested ideals in a Noetherian ring complete along the smaller ideal and admitting a
canonical dualizing complex, completion induces a bijection on germs of morphisms between
coherent modules on any neighborhood of the smaller ideal's vanishing locus in the complement
of the larger ideal, provided the associated-point closures of the target module satisfy the
strict local dimension bound along the larger ideal's vanishing locus. The comparison is
expressed canonically through sections of the internal Hom from the source module to the target
module and the inverse limit of its neighborhood quotient sections. -/
theorem neighborhoodHomComparison_bijective_of_associatedPointDimension
    (S : AffineAlgebraizationSetup A)
    (h_dualizing : CategoryTheory.DerivedCategory.HasCanonicalDualizingComplex A)
    [IsAdicComplete S.I A]
    (V : OpenNeighborhoods S)
    (F G : RingedSpace.Coh (toScheme V.val).toRingedSpace)
    (h_dimension : ∀ x : V.val, x ∈ associatedPoints F.obj →
      (V.val.ι ≫ S.U.ι) x ∉ (idealSheafDataOfIdealOnSpec S.I).support →
        ¬ Set.range (PointClosure.ι ((V.val.ι ≫ S.U.ι) x)) ∩
            (idealSheafDataOfIdealOnSpec S.I).support ⊆ S.U.compl →
          ∀ z : PointClosure.scheme ((V.val.ι ≫ S.U.ι) x),
            PointClosure.ι ((V.val.ι ≫ S.U.ι) x) z ∈ S.U.compl →
              ((Ideal.LocalCohomology.dimension S.I
                  S.I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim
                    ((PointClosure.scheme ((V.val.ι ≫ S.U.ι) x)).presheaf.stalk z))) :
    Function.Bijective
      (Scheme.CoherentCompletion.neighborhoodComparison
        ((idealOnOpen S).comap V.val.ι)
        (Scheme.Modules.internalHom G.obj F.obj)) := sorry

/-- For a Noetherian ring complete along a principal ideal and admitting a canonical dualizing
complex, the formal global-section comparison for a coherent module on the complement of a
larger ideal is bijective if every associated-point closure outside the principal vanishing locus
that meets it outside the deleted locus has local dimension strictly greater than two along the
deleted locus. -/
theorem globalNeighborhoodComparison_bijective_of_principal
    (𝔞 : Ideal A) (f : A) (hf : f ∈ 𝔞)
    (h_dualizing : CategoryTheory.DerivedCategory.HasCanonicalDualizingComplex A)
    [IsAdicComplete (Ideal.span {f}) A]
    (F : RingedSpace.Coh ((ofPrincipal 𝔞 f hf).U.toScheme).toRingedSpace)
    (h_dimension : ∀ x : (ofPrincipal 𝔞 f hf).U, x ∈ associatedPoints F.obj →
      (ofPrincipal 𝔞 f hf).U.ι x ∉
          (idealSheafDataOfIdealOnSpec (Ideal.span {f})).support →
        ¬ Set.range (PointClosure.ι ((ofPrincipal 𝔞 f hf).U.ι x)) ∩
            (idealSheafDataOfIdealOnSpec (Ideal.span {f})).support ⊆
          (ofPrincipal 𝔞 f hf).U.compl →
          ∀ z : PointClosure.scheme ((ofPrincipal 𝔞 f hf).U.ι x),
            PointClosure.ι ((ofPrincipal 𝔞 f hf).U.ι x) z ∈
                (ofPrincipal 𝔞 f hf).U.compl →
              (2 : WithBot ℕ∞) <
                ringKrullDim
                  ((PointClosure.scheme ((ofPrincipal 𝔞 f hf).U.ι x)).presheaf.stalk z)) :
    Function.Bijective
      (globalNeighborhoodComparison (ofPrincipal 𝔞 f hf) F.obj) := sorry

end AlgebraicGeometry.AffineAlgebraizationSetup
