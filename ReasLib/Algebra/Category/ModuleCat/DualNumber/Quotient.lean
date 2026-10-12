/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Quotient
public import ReasLib.Algebra.Category.ModuleCat.DualNumber.Epsilon

@[expose] public section

/-!
# Quotients of dual-number modules by epsilon

This file owns `εM` and the base-ring module `M / εM`. Named bridges relate the image,
principal-submodule, and restricted-scalar models used by downstream change-of-rings arguments.
-/

universe u v

open CategoryTheory
open CategoryTheory.Limits
open scoped DualNumber Pointwise

namespace ModuleCat.DualNumber

variable {R : Type u} [CommRing R]

/-- The submodule `εM` of a module over the dual numbers. -/
@[stacks 05CS "epsilon multiples"]
def epsSubmodule (M : ModuleCat.{v} R[ε]) : Submodule R[ε] M :=
  LinearMap.range (epsEnd M).hom

/-- The image definition of `εM` agrees with the usual principal-submodule construction. -/
@[stacks 05CS "epsilon multiples as a principal submodule"]
theorem epsSubmodule_eq_smul_top (M : ModuleCat.{v} R[ε]) :
    epsSubmodule M = (ε : R[ε]) • (⊤ : Submodule R[ε] M) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact Submodule.smul_mem_pointwise_smul y (ε : R[ε]) ⊤ trivial
  · rw [Submodule.mem_smul_pointwise_iff_exists]
    rintro ⟨y, -, rfl⟩
    exact ⟨y, epsEnd_apply M y⟩

/-- The `R`-submodule `εM`, obtained without rebuilding a local scalar action. -/
@[stacks 05CS "epsilon multiples over the base"]
noncomputable def restrictedEpsSubmodule
    (M : ModuleCat.{v} R[ε]) : Submodule R (restrict M) :=
  ModuleCat.RestrictScalars.submodule (algebraMap R R[ε]) M (epsSubmodule M)

/-- The restricted submodule `εM` is the range of restricted multiplication by `ε`. -/
@[stacks 05CS "epsilon multiples as a restricted range"]
theorem restrictedEpsSubmodule_eq_range (M : ModuleCat.{v} R[ε]) :
    restrictedEpsSubmodule M = LinearMap.range (restrictedEpsEnd M).hom :=
  ModuleCat.RestrictScalars.submodule_range (algebraMap R R[ε]) (epsEnd M)

/-- The quotient `M / εM`, bundled as a module over the base ring. -/
@[stacks 05CS "quotient by epsilon over the base"]
noncomputable def epsQuotient (M : ModuleCat.{v} R[ε]) : ModuleCat.{v} R :=
  ModuleCat.of R (restrict M ⧸ restrictedEpsSubmodule M)

namespace EpsQuotient

/-- The canonical projection from a dual-number module, restricted to the base ring, onto its
epsilon quotient. -/
@[stacks 05CS "epsilon quotient projection"]
noncomputable def mk (M : ModuleCat.{v} R[ε]) : restrict M ⟶ epsQuotient M :=
  ModuleCat.ofHom (X := restrict M) (Y := epsQuotient M)
    (restrictedEpsSubmodule M).mkQ

/-- The epsilon-quotient projection sends an element to its quotient class. -/
@[simp]
theorem mk_apply (M : ModuleCat.{v} R[ε]) (x : restrict M) :
    (mk M).hom x = Submodule.Quotient.mk x := rfl

/-- The epsilon-quotient projection is surjective. -/
theorem mk_surjective (M : ModuleCat.{v} R[ε]) :
    Function.Surjective (mk M) :=
  Submodule.mkQ_surjective _

/-- The kernel of the epsilon-quotient projection is `εM`. -/
theorem ker_mk (M : ModuleCat.{v} R[ε]) :
    LinearMap.ker (mk M).hom = restrictedEpsSubmodule M :=
  Submodule.ker_mkQ _

/-- Restricted multiplication by `ε` followed by the epsilon-quotient projection is exact. -/
@[stacks 05CS "exact epsilon quotient sequence"]
theorem exact_restrictedEpsEnd_mk (M : ModuleCat.{v} R[ε]) :
    Function.Exact (restrictedEpsEnd M) (mk M) := by
  rw [LinearMap.exact_iff, ker_mk, restrictedEpsSubmodule_eq_range]

/-- Restricted multiplication by `ε` followed by the epsilon-quotient projection is zero. -/
@[simp]
theorem restrictedEpsEnd_comp_mk (M : ModuleCat.{v} R[ε]) :
    restrictedEpsEnd M ≫ mk M = 0 := by
  apply ModuleCat.hom_ext
  exact (exact_restrictedEpsEnd_mk M).linearMap_comp_eq_zero

/-- A base-linear map killing `εM` descends to the epsilon quotient. -/
@[stacks 05CS "epsilon quotient lift"]
noncomputable def lift {M : ModuleCat.{v} R[ε]} {N : ModuleCat.{v} R}
    (f : restrict M ⟶ N)
    (hf : restrictedEpsSubmodule M ≤ LinearMap.ker f.hom) :
    epsQuotient M ⟶ N :=
  ModuleCat.ofHom <| (restrictedEpsSubmodule M).liftQ f.hom hf

/-- The lift from the epsilon quotient has the prescribed value on representatives. -/
@[simp]
theorem lift_mk {M : ModuleCat.{v} R[ε]} {N : ModuleCat.{v} R}
    (f : restrict M ⟶ N)
    (hf : restrictedEpsSubmodule M ≤ LinearMap.ker f.hom) (x : restrict M) :
    (lift f hf).hom (Submodule.Quotient.mk x) = f.hom x := rfl

/-- The epsilon-quotient projection followed by its induced lift is the original map. -/
@[simp]
theorem mk_comp_lift {M : ModuleCat.{v} R[ε]} {N : ModuleCat.{v} R}
    (f : restrict M ⟶ N)
    (hf : restrictedEpsSubmodule M ≤ LinearMap.ker f.hom) :
    mk M ≫ lift f hf = f := by
  apply ModuleCat.hom_ext
  exact Submodule.liftQ_mkQ _ _ _

/-- Morphisms out of the epsilon quotient are determined by their composites with the quotient
projection. -/
@[ext]
theorem hom_ext {M : ModuleCat.{v} R[ε]} {N : ModuleCat.{v} R}
    {f g : epsQuotient M ⟶ N} (h : mk M ≫ f = mk M ≫ g) : f = g := by
  apply ModuleCat.hom_ext
  apply Submodule.linearMap_qext
  exact ModuleCat.hom_ext_iff.mp h

/-- The induced lift is the unique map with the prescribed composite from the original module. -/
theorem lift_unique {M : ModuleCat.{v} R[ε]} {N : ModuleCat.{v} R}
    (f : restrict M ⟶ N)
    (hf : restrictedEpsSubmodule M ≤ LinearMap.ker f.hom)
    (g : epsQuotient M ⟶ N) (hg : mk M ≫ g = f) : g = lift f hf :=
  hom_ext (hg.trans (mk_comp_lift f hf).symm)

/-- The canonical epsilon-quotient projection, regarded as a cokernel cofork of multiplication by
`ε`. -/
@[stacks 05CS "epsilon quotient cokernel cofork"]
noncomputable def cokernelCofork (M : ModuleCat.{v} R[ε]) :
  CokernelCofork (restrictedEpsEnd M) :=
  CokernelCofork.ofπ (mk M) (restrictedEpsEnd_comp_mk M)

/-- The map of any cokernel cofork of multiplication by `ε` kills `εM`. -/
theorem descCondition {M : ModuleCat.{v} R[ε]}
    (s : CokernelCofork (restrictedEpsEnd M)) :
    restrictedEpsSubmodule M ≤ LinearMap.ker (Cofork.π s).hom := by
  rw [restrictedEpsSubmodule_eq_range]
  exact LinearMap.range_le_ker_iff.2 (ModuleCat.hom_ext_iff.mp s.condition)

/-- The canonical map from the epsilon quotient to any cokernel cofork of multiplication by
`ε`. -/
@[stacks 05CS "epsilon quotient cokernel descent"]
noncomputable def desc {M : ModuleCat.{v} R[ε]}
    (s : CokernelCofork (restrictedEpsEnd M)) : epsQuotient M ⟶ s.pt :=
  lift (Cofork.π s) (descCondition s)

/-- The cokernel descent map factors the cofork projection. -/
@[simp]
theorem mk_desc {M : ModuleCat.{v} R[ε]}
    (s : CokernelCofork (restrictedEpsEnd M)) :
    mk M ≫ desc s = Cofork.π s :=
  mk_comp_lift _ _

/-- The cokernel descent map is the unique map factoring the cofork projection. -/
theorem desc_unique {M : ModuleCat.{v} R[ε]}
    (s : CokernelCofork (restrictedEpsEnd M))
    (f : epsQuotient M ⟶ s.pt) (hf : mk M ≫ f = Cofork.π s) :
    f = desc s :=
  lift_unique _ _ _ hf

/-- The epsilon quotient is a cokernel of multiplication by `ε` in `ModuleCat R`. -/
@[stacks 05CS "epsilon quotient is a cokernel"]
noncomputable def cokernelIsColimit (M : ModuleCat.{v} R[ε]) :
    IsColimit (cokernelCofork M) :=
  Cofork.IsColimit.mk (cokernelCofork M) desc mk_desc desc_unique

/-- A morphism of dual-number modules maps `εM` into `εN` after restriction to the base
ring. -/
theorem map_le_comap {M N : ModuleCat.{v} R[ε]} (f : M ⟶ N) :
    restrictedEpsSubmodule M ≤
      (restrictedEpsSubmodule N).comap (restrictFunctor.map f).hom := by
  rw [restrictedEpsSubmodule_eq_range, restrictedEpsSubmodule_eq_range]
  rintro _ ⟨x, rfl⟩
  exact ⟨f x, by
    simpa using DFunLike.congr_fun
      (ModuleCat.hom_ext_iff.mp (restrictedEpsEnd_naturality f)) x⟩

/-- The morphism on epsilon quotients induced by a morphism of dual-number modules. -/
@[stacks 05CS "epsilon quotient map"]
noncomputable def map {M N : ModuleCat.{v} R[ε]} (f : M ⟶ N) :
    epsQuotient M ⟶ epsQuotient N :=
  ModuleCat.ofHom <|
    (restrictedEpsSubmodule M).mapQ (restrictedEpsSubmodule N)
      (restrictFunctor.map f).hom (map_le_comap f)

/-- The induced map on epsilon quotients sends a representative through the original map. -/
@[simp]
theorem map_mk {M N : ModuleCat.{v} R[ε]} (f : M ⟶ N) (x : restrict M) :
    (map f).hom (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (f.hom x) :
        restrict N ⧸ restrictedEpsSubmodule N) := rfl

/-- The identity morphism induces the identity on epsilon quotients. -/
@[simp]
theorem map_id (M : ModuleCat.{v} R[ε]) :
    map (𝟙 M) = 𝟙 (epsQuotient M) := by
  apply hom_ext
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- Epsilon-quotient maps preserve composition. -/
@[simp]
theorem map_comp {M N P : ModuleCat.{v} R[ε]}
    (f : M ⟶ N) (g : N ⟶ P) :
    map (f ≫ g) = map f ≫ map g := by
  apply hom_ext
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- Quotienting by `εM` as a functor from dual-number modules to modules over the base ring. -/
@[stacks 05CS "epsilon quotient functor"]
noncomputable def functor : ModuleCat.{v} R[ε] ⥤ ModuleCat.{v} R where
  obj := epsQuotient
  map := map
  map_id := map_id
  map_comp := map_comp

/-- The canonical epsilon-quotient projection is natural. -/
theorem mk_naturality {M N : ModuleCat.{v} R[ε]} (f : M ⟶ N) :
    restrictFunctor.map f ≫ mk N = mk M ≫ map f := by
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- The canonical projection from restriction to the epsilon-quotient functor. -/
@[stacks 05CS "epsilon quotient natural transformation"]
noncomputable def mkNatTrans : restrictFunctor (R := R) ⟶ functor (R := R) where
  app := mk
  naturality := fun _ _ f ↦ mk_naturality f

/-- The usual quotient by scalar multiplication with `ε`, restricted to the base ring and
bundled as a module-category object. -/
@[stacks 05CS "QuotSMulTop model of the epsilon quotient"]
noncomputable abbrev quotSMulTop (M : ModuleCat.{v} R[ε]) : ModuleCat.{v} R :=
  restrict (ModuleCat.of R[ε] (QuotSMulTop (ε : R[ε]) M))

/-- Restricting the quotient by the image definition of `εM` agrees with restricting the
principal-submodule quotient used by `QuotSMulTop`. -/
@[stacks 05CS "principal model of the epsilon quotient"]
noncomputable def principalQuotientIso (M : ModuleCat.{v} R[ε]) :
    restrict (ModuleCat.of R[ε] (M ⧸ epsSubmodule M)) ≅ quotSMulTop M :=
  (restrictFunctor (R := R)).mapIso
    (Submodule.quotEquivOfEq _ _ (epsSubmodule_eq_smul_top M)).toModuleIso

/-- The image quotient `M / εM` agrees categorically with Mathlib's `QuotSMulTop` model. -/
@[stacks 05CS "epsilon quotient comparison"]
noncomputable def isoQuotSMulTop (M : ModuleCat.{v} R[ε]) :
    epsQuotient M ≅ quotSMulTop M :=
  ModuleCat.RestrictScalars.quotientIso (algebraMap R R[ε]) M (epsSubmodule M) ≪≫
    principalQuotientIso M

/-- The linear-equivalence form of `isoQuotSMulTop`. -/
noncomputable def equivQuotSMulTop (M : ModuleCat.{v} R[ε]) :
    epsQuotient M ≃ₗ[R] quotSMulTop M :=
  (isoQuotSMulTop M).toLinearEquiv

/-- The epsilon-quotient comparison is the identity on representatives. -/
@[simp]
theorem equivQuotSMulTop_mk (M : ModuleCat.{v} R[ε]) (x : restrict M) :
    equivQuotSMulTop M (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
  change
    (Submodule.quotEquivOfEq (epsSubmodule M)
      ((ε : R[ε]) • (⊤ : Submodule R[ε] M))
      (epsSubmodule_eq_smul_top M))
        (ModuleCat.RestrictScalars.quotientEquiv
          (algebraMap R R[ε]) M (epsSubmodule M)
          (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x
  rw [ModuleCat.RestrictScalars.quotientEquiv_mk,
    Submodule.quotEquivOfEq_mk]
  rfl

/-- The inverse epsilon-quotient comparison is the identity on representatives. -/
@[simp]
theorem equivQuotSMulTop_symm_mk (M : ModuleCat.{v} R[ε]) (x : restrict M) :
    (equivQuotSMulTop M).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
  apply (equivQuotSMulTop M).injective
  simp
  rfl

end EpsQuotient

/-- The restricted and unrestricted definitions of `εM` have the same elements. -/
theorem mem_restrictedEpsSubmodule_iff
    (M : ModuleCat.{v} R[ε]) (x : restrict M) :
    x ∈ restrictedEpsSubmodule M ↔ x ∈ epsSubmodule M := Iff.rfl

end ModuleCat.DualNumber
