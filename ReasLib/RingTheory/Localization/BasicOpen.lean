/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Map
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Principal Opens and Localization Comparison Maps

This module packages the ring- and module-theoretic consequences of an
inclusion of principal opens of `PrimeSpectrum R`.  The topology remains in
the canonical `PrimeSpectrum` namespace, while the comparison maps expose the
ordinary localization data used by affine and sheaf-theoretic applications.
-/

noncomputable section

universe u v

namespace PrimeSpectrum

section

variable {R : Type u} [CommSemiring R]
variable (f g : R)

/-- An inclusion `D(g) ≤ D(f)` makes the image of `f` invertible in `R_g`. -/
@[stacks 01HS]
theorem algebraMap_isUnit_of_basicOpen_le
    (h : basicOpen g ≤ basicOpen f) :
    IsUnit (algebraMap R (Localization.Away g) f) := sorry

/-- An inclusion `D(g) ≤ D(f)` implies that a positive power of `g` is a
multiple of `f`. -/
@[stacks 01HS]
theorem exists_pow_eq_mul_of_basicOpen_le
    (h : basicOpen g ≤ basicOpen f) :
    ∃ e : ℕ, 0 < e ∧ ∃ a : R, g ^ e = a * f := sorry

/-- Inclusion of principal opens is equivalent to a positive power of the
smaller-open generator being a multiple of the larger-open generator. -/
@[stacks 01HS "principal-open inclusion criterion"]
theorem basicOpen_le_basicOpen_iff_exists_pow_eq_mul :
    basicOpen g ≤ basicOpen f ↔ ∃ e : ℕ, 0 < e ∧ ∃ a : R, g ^ e = a * f := sorry

/-- The localization comparison as an `R`-algebra homomorphism, attached to an
inclusion `D(g) ≤ D(f)`. -/
@[stacks 01HS "principal-open localization algebra map"]
noncomputable def awayToAwayAlgHom
    (h : basicOpen g ≤ basicOpen f) :
    Localization.Away f →ₐ[R] Localization.Away g :=
  IsLocalization.Away.liftAlgHom
    (S := Localization.Away f) (P := Localization.Away g) (A := R)
    (f := Algebra.ofId R (Localization.Away g)) f
    (basicOpen_le_basicOpen_iff_algebraMap_isUnit.mp h)

/-- The restriction algebra map commutes with the maps from the original semiring. -/
@[simp, stacks 01HS "principal-open localization algebra map law"]
theorem awayToAwayAlgHom_algebraMap
    (h : basicOpen g ≤ basicOpen f) (r : R) :
    awayToAwayAlgHom f g h (algebraMap R (Localization.Away f) r) =
      algebraMap R (Localization.Away g) r := sorry

/-- Restriction from a principal open to itself is the identity algebra map. -/
@[simp, stacks 01HS "principal-open localization algebra identity"]
theorem awayToAwayAlgHom_self :
    awayToAwayAlgHom f f le_rfl = AlgHom.id R (Localization.Away f) := sorry

/-- Comparison algebra homomorphisms compose along nested principal-open
inclusions. -/
@[stacks 01HS "principal-open localization algebra composition"]
theorem awayToAwayAlgHom_comp
    {q : R} (hfg : basicOpen g ≤ basicOpen f) (hgq : basicOpen q ≤ basicOpen g) :
    (awayToAwayAlgHom g q hgq).comp (awayToAwayAlgHom f g hfg) =
      awayToAwayAlgHom f q (hgq.trans hfg) := sorry

/-- The localization comparison algebra map is determined by its values on the original
semiring. -/
@[stacks 01HS "principal-open localization algebra uniqueness"]
theorem awayToAwayAlgHom_unique
    (h : basicOpen g ≤ basicOpen f)
    (phi : Localization.Away f →ₐ[R] Localization.Away g)
    (hphi : ∀ r : R,
      phi (algebraMap R (Localization.Away f) r) =
        algebraMap R (Localization.Away g) r) :
    phi = awayToAwayAlgHom f g h := sorry

/-- The localization comparison ring homomorphism `R_f → R_g` attached to
`D(g) ≤ D(f)`. -/
@[stacks 01HS]
noncomputable abbrev awayToAwayRingHom
    (h : basicOpen g ≤ basicOpen f) :
    Localization.Away f →+* Localization.Away g :=
  (awayToAwayAlgHom f g h).toRingHom

/-- The ring-hom view is definitionally the underlying hom of the restriction algebra map. -/
@[simp, stacks 01HS "principal-open localization ring bridge"]
theorem awayToAwayAlgHom_toRingHom
    (h : basicOpen g ≤ basicOpen f) :
    (awayToAwayAlgHom f g h).toRingHom = awayToAwayRingHom f g h := sorry

/-- The localization comparison `R_f → R_g` commutes with the maps from
`R`. -/
@[simp, stacks 01HS "principal-open localization ring map law"]
theorem awayToAwayRingHom_algebraMap
    (h : basicOpen g ≤ basicOpen f) (r : R) :
    awayToAwayRingHom f g h (algebraMap R (Localization.Away f) r) =
      algebraMap R (Localization.Away g) r := sorry

/-- Restriction from a principal open to itself is the identity ring homomorphism. -/
@[simp, stacks 01HS "principal-open localization ring identity"]
theorem awayToAwayRingHom_self :
    awayToAwayRingHom f f le_rfl = RingHom.id (Localization.Away f) := sorry

/-- Comparison ring homomorphisms compose along nested principal-open
inclusions. -/
@[stacks 01HS "principal-open localization ring composition"]
theorem awayToAwayRingHom_comp
    {q : R} (hfg : basicOpen g ≤ basicOpen f) (hgq : basicOpen q ≤ basicOpen g) :
    (awayToAwayRingHom g q hgq).comp (awayToAwayRingHom f g hfg) =
      awayToAwayRingHom f q (hgq.trans hfg) := sorry

/-- The localization comparison ring homomorphism is determined by its values on the original
semiring. -/
@[stacks 01HS "principal-open localization ring uniqueness"]
theorem awayToAwayRingHom_unique
    (h : basicOpen g ≤ basicOpen f)
    (phi : Localization.Away f →+* Localization.Away g)
    (hphi : ∀ r : R,
      phi (algebraMap R (Localization.Away f) r) =
        algebraMap R (Localization.Away g) r) :
    phi = awayToAwayRingHom f g h := sorry

section ModuleMap

/-- The underlying `R`-linear map used to construct restriction of a localized module from
`D(f)` to `D(g)`. -/
@[stacks 01HS "principal-open localized module linear map"]
noncomputable abbrev awayToAwayModuleLinearMap
    (M : Type v) [AddCommMonoid M] [Module R M]
    (f g : R) (h : basicOpen g ≤ basicOpen f) :
    LocalizedModule.Away f M →ₗ[R] LocalizedModule.Away g M :=
  LocalizedModule.Away.mapOfIsUnit f g
    (basicOpen_le_basicOpen_iff_algebraMap_isUnit.mp h)

/-- Restriction of a localized module to the same principal open is the identity on the
underlying `R`-module. -/
@[simp, stacks 01HS "principal-open localized module linear identity"]
theorem awayToAwayModuleLinearMap_self
    (M : Type v) [AddCommMonoid M] [Module R M] (f : R) :
    awayToAwayModuleLinearMap M f f le_rfl = LinearMap.id := sorry

/-- Underlying `R`-linear restriction maps compose along inclusions of principal opens. -/
@[stacks 01HS "principal-open localized module linear composition"]
theorem awayToAwayModuleLinearMap_comp
    (M : Type v) [AddCommMonoid M] [Module R M] (f g q : R)
    (hfg : basicOpen g ≤ basicOpen f) (hgq : basicOpen q ≤ basicOpen g) :
    (awayToAwayModuleLinearMap M g q hgq).comp
        (awayToAwayModuleLinearMap M f g hfg) =
      awayToAwayModuleLinearMap M f q (hgq.trans hfg) := sorry

/-- The underlying localized-module comparison is determined by its values on elements coming
from the original module. -/
@[stacks 01HS "principal-open localized module linear uniqueness"]
theorem awayToAwayModuleLinearMap_unique
    (M : Type v) [AddCommMonoid M] [Module R M]
    (f g : R) (h : basicOpen g ≤ basicOpen f)
    (phi : LocalizedModule.Away f M →ₗ[R] LocalizedModule.Away g M)
    (hphi : ∀ m : M,
      phi (LocalizedModule.mkLinearMap (Submonoid.powers f) M m) =
        LocalizedModule.mkLinearMap (Submonoid.powers g) M m) :
    phi = awayToAwayModuleLinearMap M f g h := sorry

/-- The underlying restriction map is semilinear over the canonical map between the localized
semirings. -/
@[stacks 01HS "principal-open localized module semilinearity"]
theorem awayToAwayModuleLinearMap_smul
    (M : Type v) [AddCommMonoid M] [Module R M]
    (f g : R) (h : basicOpen g ≤ basicOpen f) (r : Localization.Away f)
    (x : LocalizedModule.Away f M) :
    awayToAwayModuleLinearMap M f g h (r • x) =
      awayToAwayRingHom f g h r • awayToAwayModuleLinearMap M f g h x := sorry

/-- Restriction `M_f ⟶ M_g` is semilinear over the canonical localization
homomorphism `R_f ⟶ R_g`. -/
@[stacks 01HS]
noncomputable def awayToAwayModuleMap
    (M : Type v) [AddCommMonoid M] [Module R M]
    (f g : R) (h : basicOpen g ≤ basicOpen f) :
    LocalizedModule.Away f M →ₛₗ[awayToAwayRingHom f g h]
      LocalizedModule.Away g M :=
  { toFun := awayToAwayModuleLinearMap M f g h
    map_add' := (awayToAwayModuleLinearMap M f g h).map_add
    map_smul' := awayToAwayModuleLinearMap_smul M f g h }

/-- The semilinear restriction map has the underlying function of the canonical `R`-linear
restriction map. -/
@[simp, stacks 01HS "principal-open localized module map evaluation"]
theorem awayToAwayModuleMap_apply
    (M : Type v) [AddCommMonoid M] [Module R M]
    (f g : R) (h : basicOpen g ≤ basicOpen f) (x : LocalizedModule.Away f M) :
    awayToAwayModuleMap M f g h x = awayToAwayModuleLinearMap M f g h x := sorry

/-- Restriction of a localized module to the same principal open is the identity. -/
@[simp, stacks 01HS "principal-open localized module identity"]
theorem awayToAwayModuleMap_self_apply
    (M : Type v) [AddCommMonoid M] [Module R M]
    (f : R) (x : LocalizedModule.Away f M) :
    awayToAwayModuleMap M f f le_rfl x = x := sorry

/-- Semilinear restriction maps compose pointwise along inclusions of principal opens. -/
@[simp, stacks 01HS "principal-open localized module composition"]
theorem awayToAwayModuleMap_comp_apply
    (M : Type v) [AddCommMonoid M] [Module R M] (f g q : R)
    (hfg : basicOpen g ≤ basicOpen f) (hgq : basicOpen q ≤ basicOpen g)
    (x : LocalizedModule.Away f M) :
    awayToAwayModuleMap M g q hgq (awayToAwayModuleMap M f g hfg x) =
      awayToAwayModuleMap M f q (hgq.trans hfg) x := sorry

/-- The semilinear localization comparison commutes with the canonical maps from the original
module. -/
@[simp, stacks 01HS "principal-open localized module map law"]
theorem awayToAwayModuleMap_mkLinearMap
    (M : Type v) [AddCommMonoid M] [Module R M]
    (f g : R) (h : basicOpen g ≤ basicOpen f) (m : M) :
    awayToAwayModuleMap M f g h
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M m) =
      LocalizedModule.mkLinearMap (Submonoid.powers g) M m := sorry

/-- The semilinear localization comparison is determined by its values on elements coming from
the original module. -/
@[stacks 01HS "principal-open localized module map uniqueness"]
theorem awayToAwayModuleMap_unique
    (M : Type v) [AddCommMonoid M] [Module R M]
    (f g : R) (h : basicOpen g ≤ basicOpen f)
    (phi : LocalizedModule.Away f M →ₛₗ[awayToAwayRingHom f g h]
      LocalizedModule.Away g M)
    (hphi : ∀ m : M,
      phi (LocalizedModule.mkLinearMap (Submonoid.powers f) M m) =
        LocalizedModule.mkLinearMap (Submonoid.powers g) M m) :
    phi = awayToAwayModuleMap M f g h := sorry

end ModuleMap

/-- Every open cover of `D(f)` has a finite refinement indexed by a `Finset` of principal-open
generators, each contained in a member of the original cover. -/
@[stacks 01HS]
theorem basicOpen_has_finset_refinement_of_open_cover
    {ι : Type v} (U : ι → TopologicalSpace.Opens (PrimeSpectrum R))
    (hcover : basicOpen f ≤ ⨆ i, U i) :
    ∃ s : Finset R,
      basicOpen f = ⨆ g ∈ s, basicOpen g ∧
        ∀ g ∈ s, ∃ i, basicOpen g ≤ U i := sorry

/-- Every open cover of `D(f)` has a refinement by a finite indexed family of
principal opens. -/
@[stacks 01HS]
theorem basicOpen_has_finite_refinement_of_open_cover
    {ι : Type v} (U : ι → TopologicalSpace.Opens (PrimeSpectrum R))
    (hcover : basicOpen f ≤ ⨆ i, U i) :
    ∃ (sigma : Type v) (_ : Finite sigma) (g' : sigma → R),
      basicOpen f = ⨆ i, basicOpen (g' i) ∧
        ∀ i, ∃ j, basicOpen (g' i) ≤ U j := sorry

/-- A family of principal opens covers `D(f)` exactly when its generators span
the unit ideal after localizing away from `f`. -/
@[stacks 01HS]
theorem basicOpen_le_iSup_basicOpen_iff_span_eq_top
    {ι : Type v} (g' : ι → R) :
    basicOpen f ≤ ⨆ i, basicOpen (g' i) ↔
      Ideal.span (Set.range fun i : ι ↦ algebraMap R (Localization.Away f) (g' i)) = ⊤ := sorry

end

end PrimeSpectrum
