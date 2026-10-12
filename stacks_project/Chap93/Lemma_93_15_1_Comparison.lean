/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Smooth.Locus
public import ReasLib.RingTheory.AdicCompletion.Map
public import ReasLib.RingTheory.Henselian.Pair.Completion
public import stacks_project.Chap93.Lemma_93_8_7_Localization
public import stacks_project.Chap93.Lemma_93_14_3_BasedFunctor
public import stacks_project.Chap93.Lemma_93_15_1_Product

/-!
# Isolated-singularity comparison maps of ring deformation categories

The three maps
`Def_P ⥤ᵇ ∏ Def_{P_{m i}} ⥤ᵇ ∏ Def_{P_{m i}^h} ⥤ᵇ ∏ Def_{P_{m i}^∧}`
are assembled from localization, pair henselization, and adic completion,
landing in the finite product of deformation categories over `C_Λ`.
-/

@[expose] public section

open CategoryTheory Functor IsLocalRing RingPairCat Algebra PrimeSpectrum
open scoped BasedFunctor

universe u

noncomputable section

namespace FlatAlgebraCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {P : Type u} [CommRing P] [Algebra k P]
variable {ι : Type u}

/-- The local ring `P_{m i}` at a maximal ideal. -/
abbrev localRing (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (i : ι) : Type u :=
  Localization.AtPrime (m i)

/-- `localRing m i` is the localization of `P` at `m i`. -/
theorem localRing_eq (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (i : ι) :
    localRing m i = Localization.AtPrime (m i) :=
  sorry

/-- Scalar multiplication of `k` on `P_{m i}` factors through `P`. -/
theorem algebraMap_localRing (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (i : ι) (x : k) :
    algebraMap k (localRing m i) x = algebraMap P (localRing m i) (algebraMap k P x) :=
  sorry

/-- Smoothness of `Spec P ⟶ Spec k` except at the closed points `m i` is equivalent
to smoothness on the complement of `V(⨅ i, m i)`. -/
theorem nonsmooth_subset_range_iff_zeroLocus [Finite ι] (m : ι → Ideal P)
    [∀ i, (m i).IsMaximal] :
    ((smoothLocus k P)ᶜ ⊆ Set.range fun i ↦ (⟨m i, inferInstance⟩ : PrimeSpectrum P)) ↔
      (zeroLocus (⨅ i, m i : Ideal P) : Set (PrimeSpectrum P))ᶜ ⊆ smoothLocus k P :=
  sorry

variable (Λ k) in
/-- Localization at each maximal ideal, as a based functor into the product of
the local deformation categories. -/
def localizationPiBasedFunctor (m : ι → Ideal P) [∀ i, (m i).IsMaximal] :
    BasedCategory.ofFunctor (deformationForget Λ k P) ⥤ᵇ
      BasedCategory.ofFunctor (deformationPiForget Λ k (localRing m)) :=
  pairing Λ k (localRing m) (deformationForget Λ k P) fun i ↦
    { toFunctor := (localizationBasedFunctor Λ k (m i).primeCompl).toFunctor
      w := sorry }

variable (Λ k) in
/-- The underlying functor of `localizationPiBasedFunctor` retains the Artinian base. -/
theorem localizationPiBasedFunctor_obj_base (m : ι → Ideal P) [∀ i, (m i).IsMaximal]
    (ξ : deformationCategory Λ k P) :
    ((localizationPiBasedFunctor Λ k m).toFunctor.obj ξ).1 =
      (deformationForget Λ k P).obj ξ :=
  sorry

variable (Λ k) in
/-- The `i`-th factor of `localizationPiBasedFunctor` is localization at
`(m i).primeCompl`. -/
theorem localizationPiBasedFunctor_toFunctor (m : ι → Ideal P) [∀ i, (m i).IsMaximal]
    (ξ : deformationCategory Λ k P) (i : ι) :
    (evalBasedFunctor Λ k (localRing m) i).toFunctor.obj
        ((localizationPiBasedFunctor Λ k m).toFunctor.obj ξ) =
      (localizationBasedFunctor Λ k (m i).primeCompl).toFunctor.obj ξ :=
  sorry

variable [henselianPairInclusion.IsRightAdjoint]

/-- The henselization `P_{m i}^h` of the local ring at `m i`. -/
abbrev henselRing (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (i : ι) : Type u :=
  henselizationRing (pairOfIdeal (maximalIdeal (localRing m i)))

/-- `henselRing m i` is the pair henselization of `(P_{m i}, m_i P_{m i})`. -/
theorem henselRing_eq (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (i : ι) :
    henselRing m i = henselizationRing (pairOfIdeal (maximalIdeal (localRing m i))) :=
  sorry

/-- Scalar multiplication of `k` on `P_{m i}^h` factors through `P_{m i}`. -/
theorem algebraMap_henselRing (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (i : ι) (x : k) :
    algebraMap k (henselRing m i) x =
      algebraMap (localRing m i) (henselRing m i) (algebraMap k (localRing m i) x) :=
  sorry

/-- Pair henselization of a Noetherian local ring remains Noetherian. -/
instance instIsNoetherianRing_henselRing [IsNoetherianRing P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (i : ι) :
    IsNoetherianRing (henselRing m i) :=
  henselizationRing_isNoetherian (pairOfIdeal (maximalIdeal (localRing m i)))

variable (Λ k) in
/-- Pair henselization of each local ring, as a based functor of deformation
products. -/
def henselizationPiBasedFunctor (m : ι → Ideal P) [∀ i, (m i).IsMaximal] :
    BasedCategory.ofFunctor (deformationPiForget Λ k (localRing m)) ⥤ᵇ
      BasedCategory.ofFunctor (deformationPiForget Λ k (henselRing m)) :=
  deformationPiMap Λ k (localRing m) (henselRing m) fun i ↦
    henselizationBasedFunctor Λ k (localRing m i) (maximalIdeal (localRing m i))

variable (Λ k) in
/-- The underlying functor of `henselizationPiBasedFunctor` retains the Artinian base. -/
theorem henselizationPiBasedFunctor_obj_base (m : ι → Ideal P) [∀ i, (m i).IsMaximal]
    (X : deformationPi Λ k (localRing m)) :
    ((henselizationPiBasedFunctor Λ k m).toFunctor.obj X).1 = X.1 :=
  sorry

variable (Λ k) in
/-- The `i`-th factor of `henselizationPiBasedFunctor` is pair henselization of
`localRing m i` along its maximal ideal. -/
theorem henselizationPiBasedFunctor_toFunctor (m : ι → Ideal P) [∀ i, (m i).IsMaximal]
    (X : deformationPi Λ k (localRing m)) (i : ι) :
    (evalBasedFunctor Λ k (henselRing m) i).toFunctor.obj
        ((henselizationPiBasedFunctor Λ k m).toFunctor.obj X) =
      (henselizationBasedFunctor Λ k (localRing m i)
          (maximalIdeal (localRing m i))).toFunctor.obj
        (Fiber.fiberInclusion.obj (X.2 i)) :=
  sorry

/-- The extended maximal ideal of `P_{m i}` in its henselization. -/
def henselExtendedMaximalIdeal (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (i : ι) :
    Ideal (henselRing m i) :=
  Ideal.map (toHenselization (pairOfIdeal (maximalIdeal (localRing m i))))
    (maximalIdeal (localRing m i))

/-- The completion `P_{m i}^∧` of the local ring at `m i`. -/
abbrev completeRing (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (i : ι) : Type u :=
  AdicCompletion (maximalIdeal (localRing m i)) (localRing m i)

/-- `completeRing m i` is the adic completion of `P_{m i}` along its maximal ideal. -/
theorem completeRing_eq (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (i : ι) :
    completeRing m i = AdicCompletion (maximalIdeal (localRing m i)) (localRing m i) :=
  sorry

/-- Scalar multiplication of `k` on `P_{m i}^∧` factors through `P_{m i}`. -/
theorem algebraMap_completeRing (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (i : ι) (x : k) :
    algebraMap k (completeRing m i) x =
      algebraMap (localRing m i) (completeRing m i) (algebraMap k (localRing m i) x) :=
  sorry

/-- Localization of a Noetherian ring at a maximal ideal remains Noetherian. -/
instance instIsNoetherianRing_localRing [IsNoetherianRing P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (i : ι) :
    IsNoetherianRing (localRing m i) :=
  inferInstance

/-- Inverse image `J_Q = f⁻¹(J)` of `J` along the structure map of a deformation of `Q`. -/
def deformationComapIdeal {Q : Type u} [CommRing Q] [Algebra k Q] (J : Ideal Q)
    {R : FlatAlgebraCat Λ k} (f : R ⟶ ofResidue Λ k Q) : Ideal R.algebra :=
  Ideal.comap f.toRingHom J

/-- Completing a Noetherian deformation along `J_Q` remains flat over the Artinian base. -/
instance instModuleFlat_deformationCompletion {Q : Type u} [CommRing Q] [Algebra k Q]
    [IsNoetherianRing Q] (J : Ideal Q) {R : FlatAlgebraCat Λ k} (f : R ⟶ ofResidue Λ k Q) :
    Module.Flat R.base.carrier (AdicCompletion (deformationComapIdeal J f) R.algebra) :=
  sorry

/-- The completed pair `(A, R^∧)` of a deformation of `Q`. -/
def deformationCompletionObj {Q : Type u} [CommRing Q] [Algebra k Q] [IsNoetherianRing Q]
    (J : Ideal Q) {R : FlatAlgebraCat Λ k} (f : R ⟶ ofResidue Λ k Q) : FlatAlgebraCat Λ k :=
  of R.base (AdicCompletion (deformationComapIdeal J f) R.algebra)

/-- Completing a deformation does not change the Artinian local base. -/
theorem deformationCompletionObj_base {Q : Type u} [CommRing Q] [Algebra k Q]
    [IsNoetherianRing Q] (J : Ideal Q) {R : FlatAlgebraCat Λ k} (f : R ⟶ ofResidue Λ k Q) :
    (deformationCompletionObj J f).base = R.base :=
  sorry

/-- The structure map of a deformation of `Q` is adically continuous toward `J`. -/
def deformationCompletionAdicContinuous {Q : Type u} [CommRing Q] [Algebra k Q] (J : Ideal Q)
    {R : FlatAlgebraCat Λ k} (f : R ⟶ ofResidue Λ k Q) :
    f.toRingHom.AdicContinuous (deformationComapIdeal J f) J :=
  ⟨1, (pow_one (deformationComapIdeal J f)).symm ▸ Ideal.map_comap_le⟩

/-- The canonical ring map `R^∧ → Q^∧` induced by a deformation of `Q`. -/
def deformationCompletionMap {Q : Type u} [CommRing Q] [Algebra k Q] (J : Ideal Q)
    {R : FlatAlgebraCat Λ k} (f : R ⟶ ofResidue Λ k Q) :
    AdicCompletion (deformationComapIdeal J f) R.algebra →+* AdicCompletion J Q :=
  (deformationCompletionAdicContinuous J f).completionMap

/-- The completed residue arrow `(A, R^∧) ⟶ (k, Q^∧)`. -/
def deformationCompletionHom {Q : Type u} [CommRing Q] [Algebra k Q] [IsNoetherianRing Q]
    (J : Ideal Q) {R : FlatAlgebraCat Λ k} (f : R ⟶ ofResidue Λ k Q) :
    deformationCompletionObj J f ⟶ ofResidue Λ k (AdicCompletion J Q) :=
  Hom.of f.baseHom (deformationCompletionMap J f) sorry sorry

/-- Completing a deformation keeps the Artinian local base morphism. -/
theorem deformationCompletionHom_baseHom {Q : Type u} [CommRing Q] [Algebra k Q]
    [IsNoetherianRing Q] (J : Ideal Q) {R : FlatAlgebraCat Λ k} (f : R ⟶ ofResidue Λ k Q) :
    (deformationCompletionHom J f).baseHom = f.baseHom :=
  sorry

/-- Adic continuity of a morphism of deformations of `Q` between inverse images of `J`. -/
def deformationCompletionMapAdicContinuous {Q : Type u} [CommRing Q] [Algebra k Q] (J : Ideal Q)
    {ξ η : deformationCategory Λ k Q} (g : ξ ⟶ η) :
    g.left.toRingHom.AdicContinuous (deformationComapIdeal J ξ.hom)
      (deformationComapIdeal J η.hom) :=
  ⟨1, (pow_one (deformationComapIdeal J ξ.hom)).symm ▸
    Ideal.map_le_iff_le_comap.mpr
      ((le_of_eq (congrArg (fun h ↦ Ideal.comap h.toRingHom J) g.w).symm).trans
        (le_of_eq (Ideal.comap_comap g.left.toRingHom η.hom.toRingHom).symm))⟩

/-- The completed left arrow of a morphism of deformations of `Q`. -/
def deformationCompletionMapHom {Q : Type u} [CommRing Q] [Algebra k Q] [IsNoetherianRing Q]
    (J : Ideal Q) {ξ η : deformationCategory Λ k Q} (g : ξ ⟶ η) :
    deformationCompletionObj J ξ.hom ⟶ deformationCompletionObj J η.hom :=
  Hom.of g.left.baseHom (deformationCompletionMapAdicContinuous J g).completionMap sorry sorry

/-- The functor `Def_Q ⥤ Def_{AdicCompletion J Q}` completing deformations along `J`. -/
def deformationCompletionFunctor {Q : Type u} [CommRing Q] [Algebra k Q] [IsNoetherianRing Q]
    (J : Ideal Q) :
    deformationCategory Λ k Q ⥤ deformationCategory Λ k (AdicCompletion J Q) where
  obj ξ := Over.mk (deformationCompletionHom J ξ.hom)
  map g := Over.homMk (deformationCompletionMapHom J g) sorry
  map_id := sorry
  map_comp := sorry

/-- Completing deformations of `Q` commutes with forgetting to `C_Λ`. -/
theorem deformationCompletionFunctor_comp_forget {Q : Type u} [CommRing Q] [Algebra k Q]
    [IsNoetherianRing Q] (J : Ideal Q) :
    deformationCompletionFunctor J ⋙ deformationForget Λ k (AdicCompletion J Q) =
      deformationForget Λ k Q :=
  sorry

/-- Pair henselization followed by `henselizationToAdicCompletion` is the
canonical map into the adic completion. -/
theorem henselizationToAdicCompletion_comp_toHenselization
    (X : RingPairCat.{u}) [IsNoetherianRing X.ring] :
    (henselizationToAdicCompletion X).comp (toHenselization X) =
      algebraMap X.ring (AdicCompletion X.ideal X.ring) :=
  congrArg ringHom
    (((Adjunction.ofIsRightAdjoint henselianPairInclusion).homEquiv X
        ⟨adicCompletionPair X, adicCompletion_henselian X⟩).apply_symm_apply
      (toAdicCompletionPair X))

/-- Completing `P_{m i}^h` along the extended maximal ideal is adically continuous
toward the maximal ideal of `P_{m i}^∧`. -/
def henselizationToComplete_adicContinuous [IsNoetherianRing P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (i : ι) :
    (henselizationToAdicCompletion
        (pairOfIdeal (maximalIdeal (localRing m i)))).AdicContinuous
      (henselExtendedMaximalIdeal m i) (maximalIdeal (completeRing m i)) :=
  ⟨1, (pow_one (henselExtendedMaximalIdeal m i)).symm ▸
    le_of_eq
      ((Ideal.map_map
          (toHenselization (pairOfIdeal (maximalIdeal (localRing m i))))
          (henselizationToAdicCompletion
            (pairOfIdeal (maximalIdeal (localRing m i))))).trans
        ((congrArg (fun φ ↦ Ideal.map φ (maximalIdeal (localRing m i)))
            (henselizationToAdicCompletion_comp_toHenselization
              (pairOfIdeal (maximalIdeal (localRing m i))))).trans
          AdicCompletion.maximalIdeal_eq_map.symm))⟩

/-- The chosen exponent witnessing adic continuity of `P_{m i}^h → P_{m i}^∧` is `1`. -/
theorem henselizationToComplete_adicContinuous_exponent [IsNoetherianRing P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (i : ι) :
    (henselizationToComplete_adicContinuous m i).exponent = 1 :=
  sorry

/-- Comparison `(P_{m i}^h)^∧ →ₐ[k] P_{m i}^∧` induced by pair henselization. -/
def henselCompletionToCompleteRing [IsNoetherianRing P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (i : ι) :
    AdicCompletion (henselExtendedMaximalIdeal m i) (henselRing m i) →ₐ[k]
      completeRing m i where
  toRingHom :=
    (AdicCompletion.ofAlgEquiv (maximalIdeal (completeRing m i))).symm.toRingHom.comp
      (henselizationToComplete_adicContinuous m i).completionMap
  commutes' := sorry

/-- Completing the henselization recovers the completion of the local ring, via
`adicCompletion_map_toHenselization_bijective`. -/
theorem henselCompletionToCompleteRing_bijective [IsNoetherianRing P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (i : ι) :
    Function.Bijective
      (henselCompletionToCompleteRing m i :
        AdicCompletion (henselExtendedMaximalIdeal m i) (henselRing m i) →ₐ[k]
          completeRing m i) :=
  sorry

variable (Λ k) in
/-- Postcompose the residue of a deformation along a bijective `k`-algebra map of
residue rings, keeping the same Artinian local base. -/
def deformationResidueTransport {R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (φ : R →ₐ[k] S) (hφ : Function.Bijective φ.toRingHom) :
    deformationCategory Λ k R ⥤ deformationCategory Λ k S where
  obj ξ := Over.mk (ξ.hom ≫ Hom.of (𝟙 (ofResidue Λ k R).base) φ.toRingHom sorry sorry)
  map g := Over.homMk g.left sorry
  map_id := sorry
  map_comp := sorry

variable (Λ k) in
/-- Residue transport does not change the Artinian local base. -/
theorem deformationResidueTransport_obj_base {R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (φ : R →ₐ[k] S) (hφ : Function.Bijective φ.toRingHom)
    (ξ : deformationCategory Λ k R) :
    ((deformationResidueTransport Λ k φ hφ).obj ξ).left.base = ξ.left.base :=
  sorry

variable (Λ k) in
/-- The based functor `Def_{P_{m i}^h} ⥤ᵇ Def_{P_{m i}^∧}`, completing deformations
of the henselization and transporting the residue ring along
`henselizationToAdicCompletion`. -/
def completionFromHenselBasedFunctor [Algebra.FiniteType k P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (i : ι) :
    BasedCategory.ofFunctor (deformationForget Λ k (henselRing m i)) ⥤ᵇ
      BasedCategory.ofFunctor (deformationForget Λ k (completeRing m i)) :=
  -- Local instance justification (proof-local temporary data): finite type over `k` supplies Noetherianness of `P`, hence of `P_{m i}` and `P_{m i}^h` via the named instances; `k` is not determined from the hensel ring, so this cannot be a global instance.
  letI := Algebra.FiniteType.isNoetherianRing k P
  { toFunctor :=
      deformationCompletionFunctor (henselExtendedMaximalIdeal m i) ⋙
        deformationResidueTransport Λ k (henselCompletionToCompleteRing m i)
          (henselCompletionToCompleteRing_bijective m i)
    w := sorry }

variable (Λ k) in
/-- Adic completion of each henselian local ring, as a based functor of
deformation products landing in `∏ Def_{P_{m i}^∧}`. -/
def completionPiBasedFunctor [Algebra.FiniteType k P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal] :
    BasedCategory.ofFunctor (deformationPiForget Λ k (henselRing m)) ⥤ᵇ
      BasedCategory.ofFunctor (deformationPiForget Λ k (completeRing m)) :=
  deformationPiMap Λ k (henselRing m) (completeRing m)
    (completionFromHenselBasedFunctor Λ k m)

variable (Λ k) in
/-- The underlying functor of `completionPiBasedFunctor` retains the Artinian base. -/
theorem completionPiBasedFunctor_obj_base [Algebra.FiniteType k P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal]
    (X : deformationPi Λ k (henselRing m)) :
    ((completionPiBasedFunctor Λ k m).toFunctor.obj X).1 = X.1 :=
  sorry

variable (Λ k) in
/-- The `i`-th factor of `completionPiBasedFunctor` is the henselization-to-completion
transport `completionFromHenselBasedFunctor`. -/
theorem completionPiBasedFunctor_toFunctor [Algebra.FiniteType k P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal]
    (X : deformationPi Λ k (henselRing m)) (i : ι) :
    (evalBasedFunctor Λ k (completeRing m) i).toFunctor.obj
        ((completionPiBasedFunctor Λ k m).toFunctor.obj X) =
      (completionFromHenselBasedFunctor Λ k m i).toFunctor.obj
        (Fiber.fiberInclusion.obj (X.2 i)) :=
  sorry

end FlatAlgebraCat

end
