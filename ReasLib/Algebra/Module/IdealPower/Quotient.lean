module

public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.InverseSystem.Positive.Sequential
public import ReasLib.RingTheory.AdicCompletion.QuotientSystem.Limits
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Restrict
public import ReasLib.LinearAlgebra.QuotientByIdeal.QuotientRing
public import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ideal-power quotients of modules

This file owns the exact-power quotient `M / I ^ n M` and the positive sequential facade used by
the chapter, whose `n`th object is the exact-power quotient at exponent `n + 1`.
@stack 0EGS
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace Ideal

variable {R : Type u} [CommRing R]

/-- The exact-power quotient `M / I ^ n M`. -/
@[stacks 0EGS "exact ideal-power quotient of a module"]
abbrev PowerQuotient (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) : Type v :=
  M ⧸ (I ^ n) • (⊤ : Submodule R M)

namespace PowerQuotient

/-- The ideal used for the exact exponent `n` quotient. -/
@[stacks 0EGS "ideal power at an exact quotient stage"]
abbrev powerIdeal (I : Ideal R) (n : ℕ) : Ideal R := I ^ n

/-- The exact-power quotient as a bundled module-category object. -/
@[stacks 0EGS "bundled exact ideal-power quotient"]
abbrev stage (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) : ModuleCat.{v} R :=
  ModuleCat.of R (PowerQuotient I M n)

/-- The exact quotient `M / I ^ n M`, bundled over the quotient ring `R / I ^ n`.

This is the canonical stage owner for reduced modules.  The older `stage` view keeps the same
carrier as an `R`-module; downstream constructions that use the reduced ring should use this
quotient-ring view so that scalar actions are inferred from one shared instance. -/
@[stacks 0EGS "exact ideal-power quotient over its quotient ring"]
abbrev stageOver (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) :
    ModuleCat.{v} (R ⧸ powerIdeal I n) :=
  ModuleCat.of (R ⧸ powerIdeal I n)
    ((M : Type v) ⧸ (powerIdeal I n • (⊤ : Submodule R (M : Type v))))

/-- The quotient-ring stage, regarded again as an `R`-module by restriction of scalars.

This is the canonical target for comparing the legacy `R`-module view `stage I M n` with the
quotient-ring owner `stageOver I M n`. -/
@[stacks 0EGS "scalar-restricted exact ideal-power quotient stage"]
abbrev restrictedStage (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) : ModuleCat.{v} R :=
  (ModuleCat.restrictScalars (Ideal.Quotient.mk (powerIdeal I n))).obj (stageOver I M n)

/-- The canonical identity-on-carrier isomorphism from the direct `R`-module quotient stage to
the quotient-ring stage restricted back to `R`. -/
@[stacks 0EGS "direct and scalar-restricted exact quotient stages agree"]
noncomputable def stageIsoRestricted (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) :
    stage I M n ≅ restrictedStage I M n :=
  (ModuleCat.RestrictScalars.identityIso
    (R := R) (S := R ⧸ powerIdeal I n) (PowerQuotient I M n)).symm

/-- The forward map of `stageIsoRestricted` is the identity on quotient classes. -/
@[simp, stacks 0EGS "forward identity formula for exact quotient stages"]
theorem stageIsoRestricted_hom_apply (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ)
    (x : stage I M n) :
    (stageIsoRestricted I M n).hom x = x := sorry

/-- The inverse map of `stageIsoRestricted` is the identity on quotient classes. -/
@[simp, stacks 0EGS "inverse identity formula for exact quotient stages"]
theorem stageIsoRestricted_inv_apply (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ)
    (x : restrictedStage I M n) :
    (stageIsoRestricted I M n).inv x = x := sorry

/-- The canonical quotient map into an exact quotient stage. -/
@[stacks 0EGS "exact ideal-power quotient map"]
abbrev mk (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) :
    (M : Type v) →ₗ[R] (stageOver I M n : Type v) :=
  Submodule.mkQ (powerIdeal I n • (⊤ : Submodule R (M : Type v)))

/-- The exact-stage quotient map sends a representative to its quotient class. -/
@[simp, stacks 0EGS "exact ideal-power quotient map on representatives"]
theorem mk_apply (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) (x : M) :
    mk I M n x = (Submodule.Quotient.mk x : stageOver I M n) := sorry

/-- Mapping the `I ^ n` denominator back through the inclusion of the `I ^ c` power
recovers the ambient denominator whenever `c ≤ n`. -/
@[stacks 0EGS "ideal-power denominator under a submodule inclusion"]
theorem map_comap_pow_smul_top
    (I : Ideal R) (M : ModuleCat.{v} R) {c n : ℕ} (h : c ≤ n) :
    ((I ^ n • (⊤ : Submodule R (M : Type v))).comap
      (I ^ c • (⊤ : Submodule R (M : Type v))).subtype).map
        (I ^ c • (⊤ : Submodule R (M : Type v))).subtype =
      I ^ n • (⊤ : Submodule R (M : Type v)) := sorry

/-- An `R`-linear map induces the canonical map between exact quotient stages. -/
@[stacks 0EGS "map between exact ideal-power quotient stages"]
noncomputable def map
    (I : Ideal R) (M N : ModuleCat.{v} R) (n : ℕ)
    (f : (M : Type v) →ₗ[R] (N : Type v)) :
    stageOver I M n ⟶ stageOver I N n :=
  ModuleCat.ofHom (LinearMap.IdealQuotient.map f (powerIdeal I n))

/-- The exact-stage map commutes with quotient maps. -/
@[simp, stacks 0EGS "exact-stage map on quotient representatives"]
theorem map_mk
    (I : Ideal R) (M N : ModuleCat.{v} R) (n : ℕ)
    (f : (M : Type v) →ₗ[R] (N : Type v)) (x : M) :
    (map I M N n f).hom (mk I M n x) = mk I N n (f x) := sorry

/-- The canonical quotient-ring map, regarded as an `R`-linear map after restriction of
scalars. -/
@[stacks 0EGS "scalar-restricted map between exact quotient stages"]
abbrev restrictedMap (I : Ideal R) {M N : ModuleCat.{v} R}
    (f : M ⟶ N) (n : ℕ) : restrictedStage I M n ⟶ restrictedStage I N n :=
  (ModuleCat.restrictScalars (Ideal.Quotient.mk (powerIdeal I n))).map
    (map I M N n f.hom)

/-- The map on direct `R`-module quotient stages, obtained by transporting the canonical
quotient-ring map across `stageIsoRestricted`. -/
@[stacks 0EGS "functoriality on exact ideal-power quotient stages"]
noncomputable def stageMap (I : Ideal R) {M N : ModuleCat.{v} R}
    (f : M ⟶ N) (n : ℕ) : stage I M n ⟶ stage I N n :=
  (stageIsoRestricted I M n).hom ≫ restrictedMap I f n ≫
    (stageIsoRestricted I N n).inv

/-- The scalar-restricted exact-stage map sends a quotient representative to the quotient class
of its image. -/
@[simp, stacks 0EGS "scalar-restricted exact-stage map on representatives"]
theorem restrictedMap_mk (I : Ideal R) {M N : ModuleCat.{v} R}
    (f : M ⟶ N) (n : ℕ) (x : M) :
    (restrictedMap I f n).hom (mk I M n x) = mk I N n (f.hom x) := sorry

/-- The map on direct exact quotient stages sends a quotient representative to the quotient
class of its image. -/
@[simp, stacks 0EGS "direct exact-stage map on representatives"]
theorem stageMap_mk (I : Ideal R) {M N : ModuleCat.{v} R}
    (f : M ⟶ N) (n : ℕ) (x : M) :
    (stageMap I f n).hom (Submodule.Quotient.mk x : stage I M n) =
      (Submodule.Quotient.mk (f.hom x) : stage I N n) := sorry

/-- The identity-on-carrier comparison between the two exact-stage views is natural in the
module. -/
@[stacks 0EGS "naturality of the exact quotient-stage comparison"]
theorem stageIsoRestricted_naturality (I : Ideal R) {M N : ModuleCat.{v} R}
    (f : M ⟶ N) (n : ℕ) :
    stageMap I f n ≫ (stageIsoRestricted I N n).hom =
      (stageIsoRestricted I M n).hom ≫ restrictedMap I f n := sorry

/-- An `R`-linear map into an exact quotient stage descends to the quotient source. -/
@[stacks 0EGS "descent between exact ideal-power quotient stages"]
noncomputable def descend
    (I : Ideal R) (M N : ModuleCat.{v} R) (n : ℕ)
    (f : (M : Type v) →ₗ[R] (stageOver I N n : Type v))
    (hf : powerIdeal I n • (⊤ : Submodule R (M : Type v)) ≤ LinearMap.ker f) :
    stageOver I M n ⟶ stageOver I N n :=
  ModuleCat.ofHom (LinearMap.IdealQuotient.descend (powerIdeal I n) f hf)

/-- The descended exact-stage map agrees with the prescribed map on representatives. -/
@[simp, stacks 0EGS "exact-stage descent on quotient representatives"]
theorem descend_mk
    (I : Ideal R) (M N : ModuleCat.{v} R) (n : ℕ)
    (f : (M : Type v) →ₗ[R] (stageOver I N n : Type v))
    (hf : powerIdeal I n • (⊤ : Submodule R (M : Type v)) ≤ LinearMap.ker f)
    (x : M) :
    (descend I M N n f hf).hom (mk I M n x) = f x := sorry

/-- The positive quotient `M / I ^ (n + 1) M` used by the sequential facade. -/
@[stacks 0EGS "positive ideal-power quotient of a module"]
abbrev positive (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) : Type v :=
  PowerQuotient I M (n + 1)

/-- The positive quotient as a bundled module-category object. -/
@[stacks 0EGS "positive bundled ideal-power quotient"]
abbrev positiveStage (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) : ModuleCat.{v} R :=
  stage I M (n + 1)

/-- The positive quotient stage, bundled over its quotient ring. -/
@[stacks 0EGS "positive ideal-power quotient over its quotient ring"]
abbrev positiveStageOver (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) :
    ModuleCat.{v} (R ⧸ powerIdeal I (n + 1)) :=
  stageOver I M (n + 1)

/-- The positive quotient-ring stage, regarded again as an `R`-module by restriction of
scalars. -/
@[stacks 0EGS "scalar-restricted positive ideal-power quotient stage"]
abbrev positiveRestrictedStage (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) :
    ModuleCat.{v} R :=
  restrictedStage I M (n + 1)

/-- The canonical identity-on-carrier comparison between the direct and quotient-ring views of
a positive quotient stage. -/
@[stacks 0EGS "direct and scalar-restricted positive quotient stages agree"]
def positiveStageIsoRestricted (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) :
    positiveStage I M n ≅ positiveRestrictedStage I M n :=
  stageIsoRestricted I M (n + 1)

/-- The forward map of `positiveStageIsoRestricted` is the identity on quotient classes. -/
@[simp, stacks 0EGS "forward identity formula for positive quotient stages"]
theorem positiveStageIsoRestricted_hom_apply
    (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) (x : positiveStage I M n) :
    (positiveStageIsoRestricted I M n).hom x = x := sorry

/-- The inverse map of `positiveStageIsoRestricted` is the identity on quotient classes. -/
@[simp, stacks 0EGS "inverse identity formula for positive quotient stages"]
theorem positiveStageIsoRestricted_inv_apply
    (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) (x : positiveRestrictedStage I M n) :
    (positiveStageIsoRestricted I M n).inv x = x := sorry

/-- The transition from `M / I ^ (n + 2) M` to `M / I ^ (n + 1) M`. -/
@[stacks 0EGS "positive ideal-power quotient transition"]
abbrev positiveStep (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) :
    positiveStage I M (n + 1) ⟶ positiveStage I M n :=
  AdicCompletion.positiveQuotientStepMap I M ⟨n + 1, Nat.succ_pos n⟩

/-- The sequential facade of the canonical positive ideal-power quotient system. -/
@[stacks 0EGS "positive ideal-power quotient system of a module"]
abbrev positiveSystem (I : Ideal R) (M : ModuleCat.{v} R) :
    SequentialInverseSystem (ModuleCat.{v} R) :=
  (AdicCompletion.positiveQuotientSystem I M).toSequential

/-- The object formula for the positive sequential ideal-power quotient system. -/
@[simp, stacks 0EGS "positive ideal-power quotient system object"]
theorem positiveSystem_obj (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) :
    (positiveSystem I M).obj (Opposite.op n) = positiveStage I M n := sorry

/-- The successor map formula for the positive sequential ideal-power quotient system. -/
@[simp, stacks 0EGS "positive ideal-power quotient system transition"]
theorem positiveSystem_stepMap (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) :
    (positiveSystem I M).stepMap n = positiveStep I M n := sorry

/-- The map on the `n`th positive ideal-power quotient induced by a module morphism. -/
@[stacks 0EGS "functoriality on positive ideal-power quotient stages"]
noncomputable def positiveMapApp (I : Ideal R) {M N : ModuleCat.{v} R}
    (f : M ⟶ N) (n : ℕ) : positiveStage I M n ⟶ positiveStage I N n :=
  ModuleCat.ofHom ((f.hom.reduceModIdeal (I ^ (n + 1))).restrictScalars R)

/-- The canonical quotient-ring map on a positive stage, regarded as an `R`-linear map after
restriction of scalars. -/
@[stacks 0EGS "scalar-restricted map between positive quotient stages"]
abbrev positiveRestrictedMap (I : Ideal R) {M N : ModuleCat.{v} R}
    (f : M ⟶ N) (n : ℕ) :
    positiveRestrictedStage I M n ⟶ positiveRestrictedStage I N n :=
  restrictedMap I f (n + 1)

/-- The map on a positive quotient stage sends the class of `x` to the class of `f x`. -/
@[simp, stacks 0EGS "positive quotient-stage map on representatives"]
theorem positiveMapApp_mk (I : Ideal R) {M N : ModuleCat.{v} R}
    (f : M ⟶ N) (n : ℕ) (x : M) :
    (positiveMapApp I f n).hom (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (f.hom x) : positiveStage I N n) := sorry

/-- The scalar-restricted positive-stage map sends a quotient representative to the quotient
class of its image. -/
@[simp, stacks 0EGS "scalar-restricted positive-stage map on representatives"]
theorem positiveRestrictedMap_mk (I : Ideal R) {M N : ModuleCat.{v} R}
    (f : M ⟶ N) (n : ℕ) (x : M) :
    (positiveRestrictedMap I f n).hom (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (f.hom x) : positiveRestrictedStage I N n) := sorry

/-- The exact-stage map at exponent `n + 1` is the canonical positive-stage map. -/
@[simp, stacks 0EGS "exact-stage functoriality at a positive exponent"]
theorem stageMap_succ (I : Ideal R) {M N : ModuleCat.{v} R}
    (f : M ⟶ N) (n : ℕ) :
    stageMap I f (n + 1) = positiveMapApp I f n := sorry

/-- The identity-on-carrier comparison between the two positive-stage views is natural in the
module. -/
@[stacks 0EGS "naturality of the positive quotient-stage comparison"]
theorem positiveStageIsoRestricted_naturality
    (I : Ideal R) {M N : ModuleCat.{v} R} (f : M ⟶ N) (n : ℕ) :
    positiveMapApp I f n ≫ (positiveStageIsoRestricted I N n).hom =
      (positiveStageIsoRestricted I M n).hom ≫ positiveRestrictedMap I f n := sorry

/-- Positive quotient-stage maps commute with the successor transitions. -/
@[stacks 0EGS "naturality of positive ideal-power quotient-stage maps"]
theorem positiveMapApp_naturality (I : Ideal R) {M N : ModuleCat.{v} R}
    (f : M ⟶ N) (n : ℕ) :
    positiveStep I M n ≫ positiveMapApp I f n =
      positiveMapApp I f (n + 1) ≫ positiveStep I N n := sorry

/-- The identity morphism induces the identity on every positive quotient stage. -/
@[simp, stacks 0EGS "identity on positive ideal-power quotient stages"]
theorem positiveMapApp_id (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) :
    positiveMapApp I (𝟙 M) n = 𝟙 (positiveStage I M n) := sorry

/-- Passage to a positive quotient stage preserves composition of module morphisms. -/
@[stacks 0EGS "composition on positive ideal-power quotient stages"]
theorem positiveMapApp_comp (I : Ideal R) {M N P : ModuleCat.{v} R}
    (f : M ⟶ N) (g : N ⟶ P) (n : ℕ) :
    positiveMapApp I (f ≫ g) n = positiveMapApp I f n ≫ positiveMapApp I g n := sorry

/-- A module morphism induces a natural transformation of positive ideal-power quotient
systems. -/
@[stacks 0EGS "functoriality of positive ideal-power quotient systems"]
noncomputable def positiveMap (I : Ideal R) {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    positiveSystem I M ⟶ positiveSystem I N :=
  NatTrans.ofOpSequence (fun n ↦ positiveMapApp I f n)
    (positiveMapApp_naturality I f)

/-- The component of the induced map of positive quotient systems is the corresponding reduced
module morphism. -/
@[simp, stacks 0EGS "component of a positive ideal-power quotient-system map"]
theorem positiveMap_app (I : Ideal R) {M N : ModuleCat.{v} R}
    (f : M ⟶ N) (n : ℕ) :
    (positiveMap I f).app (Opposite.op n) = positiveMapApp I f n := sorry

/-- The positive quotient-system construction preserves identity morphisms. -/
@[simp, stacks 0EGS "identity map of positive ideal-power quotient systems"]
theorem positiveMap_id (I : Ideal R) (M : ModuleCat.{v} R) :
    positiveMap I (𝟙 M) = 𝟙 (positiveSystem I M) := sorry

/-- The positive quotient-system construction preserves composition of module morphisms. -/
@[stacks 0EGS "composition of positive ideal-power quotient-system maps"]
theorem positiveMap_comp (I : Ideal R) {M N P : ModuleCat.{v} R}
    (f : M ⟶ N) (g : N ⟶ P) :
    positiveMap I (f ≫ g) = positiveMap I f ≫ positiveMap I g := sorry

/-- Positive ideal-power quotients form a functor from modules to sequential inverse systems. -/
@[stacks 0EGS "positive ideal-power quotient-system functor"]
noncomputable def positiveFunctor (I : Ideal R) :
    ModuleCat.{v} R ⥤ SequentialInverseSystem (ModuleCat.{v} R) where
  obj M := positiveSystem I M
  map f := positiveMap I f
  map_id M := positiveMap_id I M
  map_comp f g := positiveMap_comp I f g

/-- The positive quotient-system functor sends a module to its canonical positive tower. -/
@[simp, stacks 0EGS "object of the positive ideal-power quotient-system functor"]
theorem positiveFunctor_obj (I : Ideal R) (M : ModuleCat.{v} R) :
    (positiveFunctor I).obj M = positiveSystem I M := sorry

/-- The positive quotient-system functor sends a morphism to its stagewise reduction. -/
@[simp, stacks 0EGS "map of the positive ideal-power quotient-system functor"]
theorem positiveFunctor_map (I : Ideal R) {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    (positiveFunctor I).map f = positiveMap I f := sorry

/-- The forward and inverse quotient-system maps induced by an isomorphism compose to the
identity. -/
theorem positiveMapIso_hom_inv_id (I : Ideal R) {M N : ModuleCat.{v} R} (e : M ≅ N) :
    positiveMap I e.hom ≫ positiveMap I e.inv = 𝟙 (positiveSystem I M) := sorry

/-- The inverse and forward quotient-system maps induced by an isomorphism compose to the
identity. -/
theorem positiveMapIso_inv_hom_id (I : Ideal R) {M N : ModuleCat.{v} R} (e : M ≅ N) :
    positiveMap I e.inv ≫ positiveMap I e.hom = 𝟙 (positiveSystem I N) := sorry

/-- A module isomorphism induces an isomorphism of positive ideal-power quotient systems. -/
@[stacks 0EGS "isomorphism of positive ideal-power quotient systems"]
noncomputable def positiveMapIso (I : Ideal R) {M N : ModuleCat.{v} R} (e : M ≅ N) :
    positiveSystem I M ≅ positiveSystem I N where
  hom := positiveMap I e.hom
  inv := positiveMap I e.inv
  hom_inv_id := positiveMapIso_hom_inv_id I e
  inv_hom_id := positiveMapIso_inv_hom_id I e

/-- The forward component of the quotient-system isomorphism is induced stagewise by its source
isomorphism. -/
@[simp, stacks 0EGS "forward component of a positive quotient-system isomorphism"]
theorem positiveMapIso_hom_app (I : Ideal R) {M N : ModuleCat.{v} R}
    (e : M ≅ N) (n : ℕ) :
    (positiveMapIso I e).hom.app (Opposite.op n) = positiveMapApp I e.hom n := sorry

/-- The inverse component of the quotient-system isomorphism is induced stagewise by the inverse
module isomorphism. -/
@[simp, stacks 0EGS "inverse component of a positive quotient-system isomorphism"]
theorem positiveMapIso_inv_app (I : Ideal R) {M N : ModuleCat.{v} R}
    (e : M ≅ N) (n : ℕ) :
    (positiveMapIso I e).inv.app (Opposite.op n) = positiveMapApp I e.inv n := sorry

/-- The limit of the positive sequential quotient system is the adic completion. -/
@[stacks 0EGS "adic completion as a sequential ideal-power quotient limit"]
noncomputable def positiveLimitIso (I : Ideal R) (M : ModuleCat.{v} R) :
    limit (positiveSystem I M) ≅ ModuleCat.of R (AdicCompletion I M) :=
  (AdicCompletion.positiveQuotientSystem I M).toSequentialLimitIso ≪≫
    AdicCompletion.positiveQuotientLimitIso I M

/-- The inverse limit comparison projects to evaluation modulo `I ^ (n + 1)`. -/
@[stacks 0EGS "adic completion sequential projection comparison"]
theorem positiveLimitIso_inv_comp_π (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) :
    (positiveLimitIso I M).inv ≫ limit.π (positiveSystem I M) (Opposite.op n) =
      ModuleCat.ofHom (AdicCompletion.eval I M (n + 1)) := sorry

end PowerQuotient

end Ideal
