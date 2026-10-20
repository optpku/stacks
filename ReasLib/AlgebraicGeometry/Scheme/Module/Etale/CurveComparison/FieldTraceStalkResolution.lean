/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FieldFiniteHomStalk
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.InjectiveTargetAugmentation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ResidualNormalizedRootsTrace

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace FieldTraceStalkResolution
variable (k : Type u) [Field k] (n : ℕ) [hn : NeZero n]
abbrev A := ActualRootsModule.Coeff.{u} n

include hn in
/-- Baer's criterion for Z/n: an ideal is dA with d dividing n. If d maps
to y, linearity gives (n/d)y=0, hence y=dz; multiplication by z extends the
map to A. ULift transports the same regular-module injectivity. This is
injectivity over A, not injectivity of the trivial Galois representation. -/
theorem regular_injective : Injective (ModuleCat.of (A.{u} n) (A.{u} n)) := by sorry

include hn in
/-- For finite A, the field stalk of an injective A-sheaf is injective as an
A-module. By Baer, a map from an ideal has finite image, hence lands in I^U
for some open normal U. I^U is A-injective by the exact finite-quotient
induction adjunction. No restriction-of-scalars R-to-A assertion is used. -/
theorem stalk_injective
    (J : Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u + 1} (A.{u} n)))
    [Injective J] : Injective ((FieldFiniteHomStalk.stalk k (A.{u} n)).obj J) := by sorry

variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} (A.{u} n))]
variable [∀ Y : Scheme.{u}, EnoughInjectives (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (A.{u} n)))]

abbrev target := ResidualNormalizedRootsTrace.fieldTarget (k := k) n
abbrev stalk := FieldFiniteHomStalk.stalk k (A.{u} n)

/-- The actual field counit identifies this target stalk with the regular A-module. -/
def targetIso : (stalk k n).obj (target k n) ≅ ModuleCat.of (A.{u} n) (A.{u} n) where
  hom := ((FieldModuleDescent.equivalence k (A.{u} n)).counitIso.app
    (ResidualNormalizedRootsTrace.target (k := k) n)).hom.hom.hom
  inv := ((FieldModuleDescent.equivalence k (A.{u} n)).counitIso.app
    (ResidualNormalizedRootsTrace.target (k := k) n)).inv.hom.hom
  hom_inv_id := by sorry
  inv_hom_id := by sorry

theorem target_injective : Injective ((stalk k n).obj (target k n)) :=
  Injective.of_iso (targetIso k n).symm (regular_injective n)

/-- The exact stalk functor applied to the SAME field-target injective resolution. -/
def resolution : InjectiveResolution ((stalk k n).obj (target k n)) where
  cocomplex := ((stalk k n).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (injectiveResolution (target k n)).cocomplex
  injective i := stalk_injective k n ((injectiveResolution (target k n)).cocomplex.X i)
  ι := ((HomologicalComplex.singleMapHomologicalComplex (stalk k n)
    (ComplexShape.up ℕ) 0).app (target k n)).inv ≫
    ((stalk k n).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (injectiveResolution (target k n)).ι
  quasiIso := by
    exact (quasiIso_iff_comp_left
      (((HomologicalComplex.singleMapHomologicalComplex (stalk k n)
        (ComplexShape.up ℕ) 0).app (target k n)).inv)
      (((stalk k n).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (injectiveResolution (target k n)).ι)).2
      (HomologicalComplex.quasiIso_map_of_preservesHomology
        (injectiveResolution (target k n)).ι (stalk k n))

/-- A concrete contraction/comparison of the actual augmented stalk resolution.
The inverse is the standard recursive injective extension into the single A-module. -/
def augmentationEquivalence :=
  -- Local instance justification (proof-local temporary data): the actual target stalk is the regular self-injective Z/n module.
  letI := target_injective k n
  InjectiveTargetAugmentation.equivalence ((stalk k n).obj (target k n)) (resolution k n)

theorem augmentationEquivalence_hom :
    (augmentationEquivalence k n).hom = (resolution k n).ι := by
  -- Local instance justification (proof-local temporary data): this proof concerns the regular A-module stalk, not its Galois representation.
  letI := target_injective k n
  exact InjectiveTargetAugmentation.hom_eq _ _

/-- The actual shift of the stalk augmentation agrees with the stalk of the
specified degree-two field augmentation, through the canonical single and
extension compositors. -/
def augmentationArrowIso :
    Arrow.mk (HomologicalComplex.extendMap (resolution k n).ι ResidualNormalizedRootsTrace.positiveTwo) ≅
    Arrow.mk (((stalk k n).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (ResidualNormalizedRootsTrace.fieldTargetNatMap (k := k) n)) :=
  Arrow.isoMk
    (HomologicalComplex.extendSingleIso ResidualNormalizedRootsTrace.positiveTwo
      ((stalk k n).obj (target k n)) 0 2 rfl ≪≫
      ((HomologicalComplex.singleMapHomologicalComplex (stalk k n)
        (ComplexShape.up ℕ) 2).app (target k n)).symm)
    (ResidualNormalizedRootsTrace.positiveTwo.mapAppIso (stalk k n)
      (injectiveResolution (target k n)).cocomplex).symm (by sorry)

variable {D : Type*} [Category* D] [Abelian D]
variable (F : ModuleCat.{u + 1} (A.{u} n) ⥤ D) [F.Additive]

def extensionArrowIso {K L : CochainComplex (ModuleCat.{u + 1} (A.{u} n)) ℕ} (g : K ⟶ L) :
    Arrow.mk (HomologicalComplex.extendMap
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map g) ResidualNormalizedRootsTrace.positiveTwo) ≅
    Arrow.mk ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map
      (HomologicalComplex.extendMap g ResidualNormalizedRootsTrace.positiveTwo)) :=
  Arrow.isoMk (ResidualNormalizedRootsTrace.positiveTwo.mapAppIso F K).symm
    (ResidualNormalizedRootsTrace.positiveTwo.mapAppIso F L).symm (by sorry)

/-- Exact endpoint comparison after any additive functor; the maps are only
the specified single/extension isomorphisms and the actual augmentation. -/
def mappedAugmentationArrowIso :
    Arrow.mk (HomologicalComplex.extendMap
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (resolution k n).ι)
      ResidualNormalizedRootsTrace.positiveTwo) ≅
    Arrow.mk ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map
      (((stalk k n).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (ResidualNormalizedRootsTrace.fieldTargetNatMap (k := k) n))) :=
  extensionArrowIso n F (resolution k n).ι ≪≫
  (F.mapHomologicalComplex (ComplexShape.up ℕ)).mapArrow.mapIso (augmentationArrowIso k n)

/-- Target-specific acyclicity: Hom may be nonexact, but it preserves the
actual contraction of this injective regular-A target resolution. -/
theorem mapped_fieldTargetNatMap_quasiIso :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map
      (((stalk k n).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (ResidualNormalizedRootsTrace.fieldTargetNatMap (k := k) n))) := by
  -- Local instance justification (proof-local temporary data): regular A is injective at the geometric stalk, not in the Galois category.
  letI := target_injective k n
  -- Local instance justification (proof-local temporary data): this specific augmentation is a homotopy equivalence after F, with no exactness assumption on F.
  letI := InjectiveTargetAugmentation.mapped_augmentation_quasiIso
    ((stalk k n).obj (target k n)) (resolution k n) F
  -- Local instance justification (proof-local temporary data): extension by zero in degrees preserves this mapped augmentation's quasi-isomorphism.
  letI : QuasiIso (HomologicalComplex.extendMap
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (resolution k n).ι)
      ResidualNormalizedRootsTrace.positiveTwo) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).2 inferInstance
  exact quasiIso_of_arrow_mk_iso _ _ (mappedAugmentationArrowIso k n F)

end FieldTraceStalkResolution
