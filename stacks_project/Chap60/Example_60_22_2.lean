/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Crystalline.AffineSpace

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Crystalline
open Crystalline.AffineSpace PadicPolynomial
open KaehlerDifferential.DeRham

/- Example 60.22.2. Crystalline cohomology of affine space over the prime field is
represented by the completed polynomial de Rham complex. -/
@[stacks 07LK] #check (Crystalline.AffineSpace.representedByCompletedDeRham :
  ∀ {p : ℕ} [Fact p.Prime] (r : ℕ)
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p r ⟶ (baseIdealSheaf p).subscheme)
    [HasSheafify (crisTopology p r γS h_compatible x₀) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (crisTopology p r γS h_compatible x₀) AddCommGrpCat.{0})]
    [HasGlobalSectionsFunctor (crisTopology p r γS h_compatible x₀) AddCommGrpCat.{0}]
    [IsGrothendieckAbelian (Sheaf (crisTopology p r γS h_compatible x₀) AddCommGrpCat.{0})]
    (hI : Affine.idealCompatible (Ideal.span {(p : ℤ_[p])}) (baseIdealSheaf p))
    (hγ : Affine.dividedPowersCompatible (Ideal.span {(p : ℤ_[p])}) (PadicInt.dividedPowers p)
      (baseIdealSheaf p) γS)
    (hx₀ : Affine.structureMapCompatible (baseIdealSheaf p) x₀),
    IsIsomorphic (derivedGlobalSections r γS h_compatible x₀)
      (DerivedCategory.Q.obj
        ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{0}).obj
          (((forget₂ (ModuleCat.{0} ℤ_[p]) AddCommGrpCat.{0}).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj (completedDeRham p r)))))

#check (Crystalline.AffineSpace.cohomologyIsoCompletedDeRham :
  ∀ {p : ℕ} [Fact p.Prime] (r : ℕ)
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p r ⟶ (baseIdealSheaf p).subscheme)
    [HasSheafify (crisTopology p r γS h_compatible x₀) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (crisTopology p r γS h_compatible x₀) AddCommGrpCat.{0})]
    (hI : Affine.idealCompatible (Ideal.span {(p : ℤ_[p])}) (baseIdealSheaf p))
    (hγ : Affine.dividedPowersCompatible (Ideal.span {(p : ℤ_[p])}) (PadicInt.dividedPowers p)
      (baseIdealSheaf p) γS)
    (hx₀ : Affine.structureMapCompatible (baseIdealSheaf p) x₀) (i : ℕ),
    IsIsomorphic (cohomology r γS h_compatible x₀ i)
      ((forget₂ (ModuleCat.{0} ℤ_[p]) AddCommGrpCat.{0}).obj
        ((completedDeRham p r).homology i)))

#check (Crystalline.AffineSpace.vanishesAbove :
  ∀ {p : ℕ} [Fact p.Prime] (r : ℕ)
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p r ⟶ (baseIdealSheaf p).subscheme)
    [HasSheafify (crisTopology p r γS h_compatible x₀) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (crisTopology p r γS h_compatible x₀) AddCommGrpCat.{0})]
    (hI : Affine.idealCompatible (Ideal.span {(p : ℤ_[p])}) (baseIdealSheaf p))
    (hγ : Affine.dividedPowersCompatible (Ideal.span {(p : ℤ_[p])}) (PadicInt.dividedPowers p)
      (baseIdealSheaf p) γS)
    (hx₀ : Affine.structureMapCompatible (baseIdealSheaf p) x₀)
    (hr : 0 < r) (i : ℕ) (hi : r < i),
    Limits.IsZero (cohomology r γS h_compatible x₀ i))

#check (Crystalline.AffineSpace.cohomologyZero :
  ∀ {p : ℕ} [Fact p.Prime] (r : ℕ)
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p r ⟶ (baseIdealSheaf p).subscheme)
    [HasSheafify (crisTopology p r γS h_compatible x₀) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (crisTopology p r γS h_compatible x₀) AddCommGrpCat.{0})]
    (hI : Affine.idealCompatible (Ideal.span {(p : ℤ_[p])}) (baseIdealSheaf p))
    (hγ : Affine.dividedPowersCompatible (Ideal.span {(p : ℤ_[p])}) (PadicInt.dividedPowers p)
      (baseIdealSheaf p) γS)
    (hx₀ : Affine.structureMapCompatible (baseIdealSheaf p) x₀) (hr : 0 < r),
    IsIsomorphic (cohomology r γS h_compatible x₀ 0) (AddCommGrpCat.of ℤ_[p]))

#check (Crystalline.AffineSpace.topInfinite :
  ∀ {p : ℕ} [Fact p.Prime] (r : ℕ)
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p r ⟶ (baseIdealSheaf p).subscheme)
    [HasSheafify (crisTopology p r γS h_compatible x₀) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (crisTopology p r γS h_compatible x₀) AddCommGrpCat.{0})]
    (hI : Affine.idealCompatible (Ideal.span {(p : ℤ_[p])}) (baseIdealSheaf p))
    (hγ : Affine.dividedPowersCompatible (Ideal.span {(p : ℤ_[p])}) (PadicInt.dividedPowers p)
      (baseIdealSheaf p) γS)
    (hx₀ : Affine.structureMapCompatible (baseIdealSheaf p) x₀) (hr : 0 < r),
    Infinite (cohomology r γS h_compatible x₀ r : Type))

#check (Crystalline.AffineSpace.topNotTorsion :
  ∀ {p : ℕ} [Fact p.Prime] (r : ℕ)
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p r ⟶ (baseIdealSheaf p).subscheme)
    [HasSheafify (crisTopology p r γS h_compatible x₀) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (crisTopology p r γS h_compatible x₀) AddCommGrpCat.{0})]
    (hI : Affine.idealCompatible (Ideal.span {(p : ℤ_[p])}) (baseIdealSheaf p))
    (hγ : Affine.dividedPowersCompatible (Ideal.span {(p : ℤ_[p])}) (PadicInt.dividedPowers p)
      (baseIdealSheaf p) γS)
    (hx₀ : Affine.structureMapCompatible (baseIdealSheaf p) x₀) (hr : 0 < r),
    ¬ AddMonoid.IsTorsion (cohomology r γS h_compatible x₀ r : Type))

#check (Crystalline.AffineSpace.topNotHausdorff :
  ∀ {p : ℕ} [Fact p.Prime] (r : ℕ)
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p r ⟶ (baseIdealSheaf p).subscheme)
    [HasSheafify (crisTopology p r γS h_compatible x₀) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (crisTopology p r γS h_compatible x₀) AddCommGrpCat.{0})]
    (hI : Affine.idealCompatible (Ideal.span {(p : ℤ_[p])}) (baseIdealSheaf p))
    (hγ : Affine.dividedPowersCompatible (Ideal.span {(p : ℤ_[p])}) (PadicInt.dividedPowers p)
      (baseIdealSheaf p) γS)
    (hx₀ : Affine.structureMapCompatible (baseIdealSheaf p) x₀) (hr : 0 < r),
    ¬ IsHausdorff (Ideal.span ({(p : ℤ)} : Set ℤ))
        (cohomology r γS h_compatible x₀ r : Type))

/- The class of η yields a copy of the p-adic field in crystalline H¹. -/
#check (Crystalline.AffineSpace.existsInjectivePadicRatCohomology :
  ∀ {p : ℕ} [Fact p.Prime]
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p 1 ⟶ (baseIdealSheaf p).subscheme)
    [HasSheafify (crisTopology p 1 γS h_compatible x₀) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (crisTopology p 1 γS h_compatible x₀) AddCommGrpCat.{0})]
    (hI : Affine.idealCompatible (Ideal.span {(p : ℤ_[p])}) (baseIdealSheaf p))
    (hγ : Affine.dividedPowersCompatible (Ideal.span {(p : ℤ_[p])}) (PadicInt.dividedPowers p)
      (baseIdealSheaf p) γS)
    (hx₀ : Affine.structureMapCompatible (baseIdealSheaf p) x₀),
    ∃ f : ℚ_[p] →+ (cohomology 1 γS h_compatible x₀ 1 : Type),
      Function.Injective f)

/- Polynomial presentation, canonical divided powers, and the completed envelope. -/

#check (PadicPolynomial.modP :
  ∀ (p r : ℕ) [Fact p.Prime],
    polynomialRing p r →ₐ[ℤ_[p]] coordinateRing p r)

#check (PadicPolynomial.ker_modP_eq_span_p :
  ∀ (p r : ℕ) [Fact p.Prime],
    RingHom.ker (modP p r).toRingHom = Ideal.span {(p : polynomialRing p r)})

#check (PadicPolynomial.dividedPowersPrime :
  ∀ (p r : ℕ) [Fact p.Prime],
    DividedPowers (Ideal.span {(p : polynomialRing p r)}))

#check (PadicPolynomial.dividedPowersPrime_dpow :
  ∀ (p r n : ℕ) [Fact p.Prime] (a : polynomialRing p r),
    (dividedPowersPrime p r).dpow n ((p : polynomialRing p r) * a) =
      algebraMap ℤ_[p] (polynomialRing p r)
          ((PadicInt.dividedPowers p).dpow n (p : ℤ_[p])) * a ^ n)

#check (PadicPolynomial.envelope_isUniversal :
  ∀ (p r : ℕ) [Fact p.Prime],
    DividedPowerEnvelope.IsUniversal (PadicInt.dividedPowers p)
      (algebraMap ℤ_[p] (polynomialRing p r)) (primeMap_le p r) (envelope p r))

#check (PadicPolynomial.envelope_completion_eq :
  ∀ (p r : ℕ) [Fact p.Prime],
    principalAdicCompletion (p : (envelope p r).D) =
      AdicCompletion (Ideal.span {(p : polynomialRing p r)}) (polynomialRing p r))

/- The diagonal differential and the explicit completed forms on the affine line. -/

#check (PadicPolynomial.completedDeRham :
  ∀ (p r : ℕ) [Fact p.Prime],
    CochainComplex (ModuleCat.{0} ℤ_[p]) ℕ)

#check (PadicPolynomial.completedDeRham_X :
  ∀ (p r n : ℕ) [Fact p.Prime],
    (completedDeRham p r).X n = completedTerm p r n)

#check (PadicPolynomial.completedDeRham_d :
  ∀ (p r n : ℕ) [Fact p.Prime],
    (completedDeRham p r).d n (n + 1) = completedDeRhamDifferential p r n)

#check (PadicPolynomial.lineDifferential_one :
  ∀ (p : ℕ) [Fact p.Prime],
    completedDifferential p 1 0
        (AdicCompletion.of (Ideal.span {(p : ℤ_[p])}) (term ℤ_[p] (polynomialRing p 1) 0 : Type) (powerZeroForm p 0)) = 0)

#check (PadicPolynomial.lineDifferential_monomial :
  ∀ (p n : ℕ) [Fact p.Prime],
    completedDifferential p 1 0
        (AdicCompletion.of (Ideal.span {(p : ℤ_[p])}) (term ℤ_[p] (polynomialRing p 1) 0 : Type) (powerZeroForm p (n + 1))) =
      (n + 1 : ℤ_[p]) •
        AdicCompletion.of (Ideal.span {(p : ℤ_[p])}) (term ℤ_[p] (polynomialRing p 1) 1 : Type) (monomialOneForm p n))

#check (PadicPolynomial.lineHomology_equiv_coker :
  ∀ (p : ℕ) [Fact p.Prime],
    IsIsomorphic ((completedDeRham p 1).homology 1) (ModuleCat.of ℤ_[p] (lineCoker p)))

#check (PadicPolynomial.exists_injective_torsionSummand :
  ∀ (p : ℕ) [Fact p.Prime],
    ∃ f : torsionSummand p →ₗ[ℤ_[p]] lineCoker p, Function.Injective f)

#check (PadicPolynomial.omegaCoeff_apply :
  ∀ (p e : ℕ) [Fact p.Prime] (he : 0 < e),
    omegaCoeff p (p ^ (2 * e) - 1) = (p : ℤ_[p]) ^ e)

#check (PadicPolynomial.omegaPartial :
  ∀ (p : ℕ) [Fact p.Prime] (N : ℕ),
    term ℤ_[p] (polynomialRing p 1) 1)

#check (PadicPolynomial.omega :
  ∀ (p : ℕ) [Fact p.Prime],
    completedForm p 1 1)

#check (PadicPolynomial.omegaClass :
  ∀ (p : ℕ) [Fact p.Prime],
    lineCoker p)

#check (PadicPolynomial.omega_not_isOfFinAddOrder :
  ∀ (p : ℕ) [Fact p.Prime],
    ¬ IsOfFinAddOrder (omegaClass p))

#check (PadicPolynomial.etaCoeff_apply :
  ∀ (p e : ℕ) [Fact p.Prime] (he : 0 < e),
    etaCoeff p (p ^ e - 1) = (p : ℤ_[p]) ^ e)

#check (PadicPolynomial.etaPartial :
  ∀ (p : ℕ) [Fact p.Prime] (N : ℕ),
    term ℤ_[p] (polynomialRing p 1) 1)

#check (PadicPolynomial.eta :
  ∀ (p : ℕ) [Fact p.Prime],
    completedForm p 1 1)

#check (PadicPolynomial.etaClass :
  ∀ (p : ℕ) [Fact p.Prime],
    lineCoker p)

#check (PadicPolynomial.etaRootPartial :
  ∀ (p : ℕ) [Fact p.Prime] (t N : ℕ),
    term ℤ_[p] (polynomialRing p 1) 1)

#check (PadicPolynomial.etaRoot :
  ∀ (p t : ℕ) [Fact p.Prime],
    completedForm p 1 1)

#check (PadicPolynomial.eta_class_mem_smul :
  ∀ (p t N : ℕ) [Fact p.Prime] (ht : 0 < t) (hN : t ≤ N),
    AdicCompletion.of (Ideal.span {(p : ℤ_[p])}) (term ℤ_[p] (polynomialRing p 1) 1 : Type) (etaPartial p N) -
        (p : ℤ_[p]) ^ t • AdicCompletion.of (Ideal.span {(p : ℤ_[p])}) (term ℤ_[p] (polynomialRing p 1) 1 : Type) (etaRootPartial p t N) ∈
      LinearMap.range (completedDifferential p 1 0))

#check (PadicPolynomial.etaClass_eq_smul :
  ∀ (p t : ℕ) [Fact p.Prime],
    etaClass p = (p : ℤ_[p]) ^ t •
      (Submodule.Quotient.mk (etaRoot p t) : lineCoker p))

#check (PadicPolynomial.eta_not_mem_range :
  ∀ (p : ℕ) [Fact p.Prime],
    eta p ∉ LinearMap.range (completedDifferential p 1 0))

#check (PadicPolynomial.etaClass_nsmul_ne_zero :
  ∀ (p m : ℕ) [Fact p.Prime] (hm : 0 < m),
    m • etaClass p ≠ 0)

#check (PadicPolynomial.etaPrimitivePartial :
  ∀ (p : ℕ) [Fact p.Prime] (a : ℤ_[p]) (N : ℕ),
    polynomialRing p 1)

#check (PadicPolynomial.etaPrimitive_not_adicCauchy :
  ∀ (p : ℕ) [Fact p.Prime] (a : ℤ_[p]),
    ¬ AdicCompletion.IsAdicCauchy (Ideal.span {(p : ℤ_[p])}) (polynomialRing p 1)
        (fun N ↦ etaPrimitivePartial p a N))

#check (PadicPolynomial.existsInjectivePadicRat :
  ∀ (p : ℕ) [Fact p.Prime],
    ∃ f : ℚ_[p] →ₗ[ℤ_[p]] lineCoker p, Function.Injective f ∧ f 1 = etaClass p)

/- Canonical APIs for surjectivity, uniqueness of divided powers, and completion of maps. -/
section CanonicalReuse

variable (p r : ℕ) [Fact p.Prime]

#check (MvPolynomial.map_surjective
    (PadicInt.toZMod : ℤ_[p] →+* ZMod p) (ZMod.ringHom_surjective PadicInt.toZMod) :
  Function.Surjective (PadicPolynomial.modP p r))

#check (PadicInt.dividedPowers_eq_of_dpow_mul :
  ∀ {gamma delta : DividedPowers (Ideal.span {(p : polynomialRing p r)})},
    (∀ (n : ℕ) (a : polynomialRing p r),
      gamma.dpow n ((p : polynomialRing p r) * a) =
        algebraMap ℤ_[p] (polynomialRing p r)
          ((PadicInt.dividedPowers p).dpow n (p : ℤ_[p])) * a ^ n) →
    (∀ (n : ℕ) (a : polynomialRing p r),
      delta.dpow n ((p : polynomialRing p r) * a) =
        algebraMap ℤ_[p] (polynomialRing p r)
          ((PadicInt.dividedPowers p).dpow n (p : ℤ_[p])) * a ^ n) →
    gamma = delta)

variable (n : ℕ)

#check (AdicCompletion.map_mk (Ideal.span {(p : ℤ_[p])})
    (d ℤ_[p] (polynomialRing p r) n).hom :
  ∀ a : AdicCompletion.AdicCauchySequence (Ideal.span {(p : ℤ_[p])})
      (term ℤ_[p] (polynomialRing p r) n : Type),
    completedDifferential p r n
        (AdicCompletion.mk (Ideal.span {(p : ℤ_[p])})
          (term ℤ_[p] (polynomialRing p r) n : Type) a) =
      AdicCompletion.mk (Ideal.span {(p : ℤ_[p])})
        (term ℤ_[p] (polynomialRing p r) (n + 1) : Type)
        (AdicCompletion.AdicCauchySequence.map (Ideal.span {(p : ℤ_[p])})
          (d ℤ_[p] (polynomialRing p r) n).hom a))

end CanonicalReuse
