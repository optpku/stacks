/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Order.WithBotTop
public import ReasLib.RingTheory.Depth.Localization
public import ReasLib.RingTheory.Ideal.Localization
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension

@[expose] public section

open CategoryTheory

universe u v

namespace Ideal.LocalCohomology

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- The depth alternative along prime chains outside, on, and inside a chosen locus. -/
def PrimeChainDepthCondition (I : Ideal A) (T : Set (PrimeSpectrum A))
    (M : Type v) [AddCommGroup M] [Module A M] (s d : ℤ) : Prop :=
  ∀ p r q : PrimeSpectrum A,
    p.asIdeal ≤ r.asIdeal → r.asIdeal ≤ q.asIdeal →
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
        r ∈ PrimeSpectrum.zeroLocus (I : Set A) → r ∉ T → q ∈ T →
          (s : EInt) ≤
              ((WithTop.map Int.ofNat
                (moduleDepth (Localization.AtPrime p.asIdeal)
                  (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) ∨
            ((d + s : ℤ) : EInt) <
              ((WithTop.map Int.ofNat
                (moduleDepth (Localization.AtPrime p.asIdeal)
                  (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) +
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim (p.asIdeal.quotientAtPrime q))

/-- The depth bound on the punctured `I`-adic completion at every prime in `T`. -/
def CompletedPuncturedDepthCondition (I : Ideal A) (T : Set (PrimeSpectrum A))
    (M : Type v) [AddCommGroup M] [Module A M] (s : ℤ) : Prop :=
  ∀ q : PrimeSpectrum A, q ∈ T →
    let A_q := Localization.AtPrime q.asIdeal
    let I_q := I.localizationAtPrime q
    let A' := AdicCompletion I_q A_q
    let M' := AdicCompletion I_q (LocalizedModule.AtPrime q.asIdeal M)
    let I' : Ideal A' := I_q.map (algebraMap A_q A')
    let m' : Ideal A' :=
      (IsLocalRing.maximalIdeal A_q).map (algebraMap A_q A')
    ∀ p' : PrimeSpectrum A',
      p' ∉ PrimeSpectrum.zeroLocus (I' : Set A') →
        PrimeSpectrum.zeroLocus p'.asIdeal ∩
            PrimeSpectrum.zeroLocus (I' : Set A') =
          {r | r.asIdeal = m'} →
          (s : EInt) <
            ((WithTop.map Int.ofNat
              (moduleDepth (Localization.AtPrime p'.asIdeal)
                (LocalizedModule.AtPrime p'.asIdeal M')) : WithTop ℤ) : EInt)

/-- A Noetherian algebraization situation packages the geometric, homological, and depth
conditions associated with an ideal, finite module, specialization-stable locus, and two
integer bounds. -/
structure AlgebraizationSituation
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (I : Ideal A) (M : Type v)
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (T : Set (PrimeSpectrum A)) (s d : ℤ) : Prop where
  /-- The subset `T` is stable under specialization. -/
  stableUnderSpecialization : StableUnderSpecialization T
  /-- Every prime in `T` contains `I`. -/
  subset_zeroLocus : T ⊆ PrimeSpectrum.zeroLocus (I : Set A)
  /-- The ring `A` admits a dualizing complex relative to `H`. -/
  hasDualizingComplex :
    ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H
  /-- The local-cohomological dimension of `(A, I)` is at most `d`. -/
  cohomologicalDimension_le : HasDimensionLE I d
  /-- The required alternative holds along every prime chain `p ≤ r ≤ q`. -/
  primeChainDepth : PrimeChainDepthCondition I T M s d
  /-- The completed localized module has depth greater than `s` at the specified primes. -/
  completedPuncturedDepth : CompletedPuncturedDepthCondition I T M s

namespace AlgebraizationSituation

/-- Assemble an algebraization situation from its six defining conditions. -/
def ofConditions
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (I : Ideal A) (M : Type v)
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (T : Set (PrimeSpectrum A)) (s d : ℤ)
    (hT : StableUnderSpecialization T)
    (hTI : T ⊆ PrimeSpectrum.zeroLocus (I : Set A))
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    (h_cd : HasDimensionLE I d)
    (h_chain : PrimeChainDepthCondition I T M s d)
    (h_completed : CompletedPuncturedDepthCondition I T M s) :
    AlgebraizationSituation H I M T s d :=
  ⟨hT, hTI, h_dualizing, h_cd, h_chain, h_completed⟩

/-- The specialization and zero-locus conditions of an algebraization situation. -/
theorem geometricConditions
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    {H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))}
    {I : Ideal A} {T : Set (PrimeSpectrum A)} {s d : ℤ}
    (h : AlgebraizationSituation H I M T s d) :
    StableUnderSpecialization T ∧ T ⊆ PrimeSpectrum.zeroLocus (I : Set A) :=
  ⟨h.stableUnderSpecialization, h.subset_zeroLocus⟩

/-- The dualizing-complex and cohomological-dimension conditions of an algebraization
situation. -/
theorem homologicalConditions
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    {H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))}
    {I : Ideal A} {T : Set (PrimeSpectrum A)} {s d : ℤ}
    (h : AlgebraizationSituation H I M T s d) :
    (∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H) ∧
      HasDimensionLE I d :=
  ⟨h.hasDualizingComplex, h.cohomologicalDimension_le⟩

/-- The prime-chain and completed punctured-depth conditions of an algebraization situation. -/
theorem depthConditions
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    {H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))}
    {I : Ideal A} {T : Set (PrimeSpectrum A)} {s d : ℤ}
    (h : AlgebraizationSituation H I M T s d) :
    PrimeChainDepthCondition I T M s d ∧
      CompletedPuncturedDepthCondition I T M s :=
  ⟨h.primeChainDepth, h.completedPuncturedDepth⟩

/-- If `p ≤ q`, with `p` outside the zero locus of `I` and `q` in `T`, and no prime
of the zero locus of `I` outside `T` lies between them, then the localized module at `p`
has depth greater than `s`. -/
theorem depth_gt_of_no_intermediate
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    {I : Ideal A} {T : Set (PrimeSpectrum A)} {s d : ℤ}
    (h : AlgebraizationSituation H I M T s d) (p q : PrimeSpectrum A)
    (hpq : p.asIdeal ≤ q.asIdeal)
    (hp : p ∉ PrimeSpectrum.zeroLocus (I : Set A)) (hq : q ∈ T)
    (h_no_intermediate : ¬ ∃ r : PrimeSpectrum A,
      r ∈ PrimeSpectrum.zeroLocus (I : Set A) ∧ r ∉ T ∧
        p.asIdeal ≤ r.asIdeal ∧ r.asIdeal ≤ q.asIdeal) :
    (s : EInt) <
      ((WithTop.map Int.ofNat
        (moduleDepth (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) := sorry

/-- If `I ≤ a`, a Noetherian ring admits a dualizing complex, the local-cohomological
dimension of `I` is at most `d`, and the strict depth alternative holds for every prime
outside `V(I)` specializing into `V(a)`, then `V(a)` defines an algebraization situation
for the finite module and integer bounds `s` and `d`. -/
theorem of_zeroLocus
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (I a : Ideal A) (hIa : I ≤ a) (s d : ℤ)
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    (h_cd : HasDimensionLE I d)
    (h_depth : ∀ p q : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) → p.asIdeal ≤ q.asIdeal →
        q ∈ PrimeSpectrum.zeroLocus (a : Set A) →
          (s : EInt) <
              ((WithTop.map Int.ofNat
                (moduleDepth (Localization.AtPrime p.asIdeal)
                  (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) ∨
            ((d + s : ℤ) : EInt) <
              ((WithTop.map Int.ofNat
                (moduleDepth (Localization.AtPrime p.asIdeal)
                  (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) +
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim (p.asIdeal.quotientAtPrime q))) :
    AlgebraizationSituation H I M (PrimeSpectrum.zeroLocus (a : Set A)) s d := sorry

end AlgebraizationSituation

end Ideal.LocalCohomology
