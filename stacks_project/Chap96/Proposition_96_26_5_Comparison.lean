/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.Algebra.Category.CommRingCat.ULift
public import ReasLib.Algebra.Homology.DerivedCategory.Completeness
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.BaseChange
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.InverseSystem.Milnor
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition
public import stacks_project.Chap87.Definition_87_4_8_WeaklyAdmissible
public import stacks_project.Chap96.Definition_96_26_1_QC
public import stacks_project.Chap96.Proposition_96_26_5_Groupoids

/-!
# Comparison of `QC(Spf(A))` with derived-complete complexes

Infinitesimal stages `Spec(A ⧸ I^{n+1})` of `Spf(A)` determine derived sections of a
quasi-coherent object. The comparison functor to `D_comp(A, I)` is the Milnor homotopy
limit of that inverse system, realized as the mapping cocone of `1 - shift` on the
product of the stage complexes in `DerivedCategory (ModuleCat.{u+1} A)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AffineFormalAlgebraicSpace
open CategoryTheory CategoryTheory.Limits CategoryTheory.Localization
open CategoryTheory.ModulesOnCategory CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {A : Type u}
variable [CommRing A] [TopologicalSpace A] [TopologicalRing.IsAdicRing A]
variable [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]

/-- Positive powers of an ideal of definition remain weak ideals of definition. -/
theorem isWeakIdealOfDefinition_pow (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    TopologicalRing.Ideal.IsWeakIdealOfDefinition (I ^ (n + 1)) :=
  sorry

/-- The weak ideal of definition `I^{n+1}` indexing the `n`th infinitesimal stage. -/
def powerStage (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (n : ℕ) : WeakIdealOfDefinition A :=
  WeakIdealOfDefinition.of (I ^ (n + 1)) (isWeakIdealOfDefinition_pow I hI n)

/-- Reverse inclusion of successive positive powers of `I`. -/
theorem powerStage_le (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (n : ℕ) : powerStage I hI n ≤ powerStage I hI (n + 1) :=
  sorry

/-- The Yoneda section of `Spf(A)` classified by the cocone leg at `I^{n+1}`. -/
def stageSection (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    (spf A structureHom).obj.obj (op (stage A structureHom (powerStage I hI n))) :=
  yonedaEquiv
    ((sheafificationAdjunction (Scheme.fppfTopology.over S) (Type u)).homEquiv
      (yoneda.obj (stage A structureHom (powerStage I hI n)))
      (spf A structureHom) (spfι A structureHom (powerStage I hI n)))

/-- The object of the discrete Grothendieck construction of `Spf(A)` lying over
`Spec(A ⧸ I^{n+1})`. -/
def stageTotalObj (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    (spfToGroupoids A structureHom).total :=
  op ⟨op (stage A structureHom (powerStage I hI n)), stageSection structureHom I hI n⟩

/-- The `n`th infinitesimal stage as an object of `𝒳_affine`. -/
def stageObj (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    affineSite (spfToGroupoids A structureHom) :=
  ⟨stageTotalObj structureHom I hI n, sorry⟩

/-- The object of `stageObj n` is `stageTotalObj n`. -/
theorem stageObj_obj (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    (stageObj structureHom I hI n).obj = stageTotalObj structureHom I hI n :=
  sorry

/-- The thickening morphism `Spec(A ⧸ I^{n+1}) ⟶ Spec(A ⧸ I^{n+2})` in `𝒳_affine`. -/
def stageHom (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    stageObj structureHom I hI n ⟶ stageObj structureHom I hI (n + 1) :=
  homMk
    (Quiver.Hom.op
      (CategoryOfElements.homMk
        ⟨op (stage A structureHom (powerStage I hI (n + 1))),
          stageSection structureHom I hI (n + 1)⟩
        ⟨op (stage A structureHom (powerStage I hI n)),
          stageSection structureHom I hI n⟩
        ((thickenings A structureHom).map (homOfLE (powerStage_le I hI n))).op sorry))

/-- The affine inclusion sends `stageHom n` to its underlying thickening arrow. -/
theorem stageHom_hom (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    (affineInclusion (spfToGroupoids A structureHom)).map
        (stageHom structureHom I hI n) =
      (stageHom structureHom I hI n).hom :=
  sorry

/-- The quotient map `A → A ⧸ I^{n+1}`, lifted to `ULift`. -/
def stageStructureRingHom (I : Ideal A) (n : ℕ) :
    A →+* ULift.{u + 1, u} (A ⧸ I ^ (n + 1)) :=
  (ULift.ringEquiv.symm :
      (A ⧸ I ^ (n + 1)) ≃+* ULift.{u + 1, u} (A ⧸ I ^ (n + 1))).toRingHom.comp
    (Ideal.Quotient.mk (I ^ (n + 1)))

/-- `stageStructureRingHom n` is the universe lift of the quotient map `A → A ⧸ I^{n+1}`. -/
theorem stageStructureRingHom_eq (I : Ideal A) (n : ℕ) :
    stageStructureRingHom I n =
      (ULift.ringEquiv.symm :
          (A ⧸ I ^ (n + 1)) ≃+* ULift.{u + 1, u} (A ⧸ I ^ (n + 1))).toRingHom.comp
        (Ideal.Quotient.mk (I ^ (n + 1))) :=
  sorry



/-- Coefficient identification of the chaotic structure sheaf at the `n`th stage with the
universe lift of `A ⧸ I^{n+1}`, via `Scheme.ΓSpecIso`. -/
def stageCoeffIso (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    (affineStructureSheaf (spfToGroupoids A structureHom)).obj.obj
        (op (stageObj structureHom I hI n)) ≅
      CommRingCat.of (ULift.{u + 1, u} (A ⧸ I ^ (n + 1))) :=
  CommRingCat.universeLift.{u, u + 1}.mapIso
    (Scheme.ΓSpecIso (.of (A ⧸ I ^ (n + 1))))

/-- The underlying rings of `stageCoeffIso` identify `𝒪(stage n)` with `ULift (A ⧸ I^{n+1})`. -/
theorem stageCoeff_eq (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    stageCoeffIso structureHom I hI n =
      CommRingCat.universeLift.{u, u + 1}.mapIso
        (Scheme.ΓSpecIso (.of (A ⧸ I ^ (n + 1)))) :=
  sorry


/-- The structure map `A → 𝒪(stage n)` is the lifted quotient map, transported along
`stageCoeffIso`. -/
def stageRingHom (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    A →+* (affineStructureSheaf (spfToGroupoids A structureHom)).obj.obj
      (op (stageObj structureHom I hI n)) :=
  (stageCoeffIso structureHom I hI n).inv.hom.comp (stageStructureRingHom I n)

/-- `stageRingHom n` is `stageStructureRingHom n` followed by `stageCoeffIso.inv`. -/
theorem stageRingHom_eq (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    stageRingHom structureHom I hI n =
      (stageCoeffIso structureHom I hI n).inv.hom.comp (stageStructureRingHom I n) :=
  sorry

/-- The ring map `𝒪(stage (n+1)) → 𝒪(stage n)` induced by `stageHom n`. -/
def stageCoeffHom (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    (affineStructureSheaf (spfToGroupoids A structureHom)).obj.obj
        (op (stageObj structureHom I hI (n + 1))) →+*
      (affineStructureSheaf (spfToGroupoids A structureHom)).obj.obj
        (op (stageObj structureHom I hI n)) :=
  ((affineStructureSheaf (spfToGroupoids A structureHom)).obj.map
      (stageHom structureHom I hI n).op).hom

/-- Iterated restriction `A → 𝒪(n+1) → 𝒪(n)` agrees with `A → 𝒪(n)`. -/
theorem stageRingHom_comp (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    (stageRingHom structureHom I hI n) =
      (stageCoeffHom structureHom I hI n).comp
        (stageRingHom structureHom I hI (n + 1)) :=
  sorry


/-- Restriction of scalars from `𝒪(stage n)` to `A`. -/
def stageRestrictScalars (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    ModuleCat.{u + 1}
        ((affineStructureSheaf (spfToGroupoids A structureHom)).obj.obj
          (op (stageObj structureHom I hI n))) ⥤
      ModuleCat.{u + 1} A :=
  ModuleCat.restrictScalars (stageRingHom structureHom I hI n)

/-- Restriction of scalars from `𝒪(stage n)` to `A` is additive. -/
instance stageRestrictScalars_additive (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    (stageRestrictScalars structureHom I hI n).Additive :=
  sorry

/-- Restriction of scalars from `𝒪(stage n)` to `A` preserves finite limits. -/
instance stageRestrictScalars_preservesFiniteLimits (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    PreservesFiniteLimits (stageRestrictScalars structureHom I hI n) :=
  sorry

/-- Restriction of scalars from `𝒪(stage n)` to `A` preserves finite colimits. -/
instance stageRestrictScalars_preservesFiniteColimits (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    PreservesFiniteColimits (stageRestrictScalars structureHom I hI n) :=
  sorry

/-- Derived restriction of scalars from `𝒪(stage n)` to `A`. -/
def stageDerivedRestrict (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    DerivedCategory
        (ModuleCat.{u + 1}
          ((affineStructureSheaf (spfToGroupoids A structureHom)).obj.obj
            (op (stageObj structureHom I hI n)))) ⥤
      DerivedCategory (ModuleCat.{u + 1} A) :=
  (stageRestrictScalars structureHom I hI n).mapDerivedCategory

/-- Derived sections at the `n`th infinitesimal stage, restricted to `A`-complexes. -/
def rGammaStage (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    QC (spfToGroupoids A structureHom) ⥤ DerivedCategory (ModuleCat.{u + 1} A) :=
  QC.inclusion (spfToGroupoids A structureHom) ⋙
    chaoticRGamma.{u + 1, u, u}
      (affineStructureSheaf (spfToGroupoids A structureHom))
      (stageObj structureHom I hI n) ⋙
    stageDerivedRestrict structureHom I hI n

/-- Objectwise, `rGammaStage n` is restriction of scalars of chaotic derived sections. -/
theorem rGammaStage_obj (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ)
    (K : QC (spfToGroupoids A structureHom)) :
    (rGammaStage structureHom I hI n).obj K =
      (stageDerivedRestrict structureHom I hI n).obj
        ((chaoticRGamma.{u + 1, u, u}
            (affineStructureSheaf (spfToGroupoids A structureHom))
            (stageObj structureHom I hI n)).obj
          ((QC.inclusion (spfToGroupoids A structureHom)).obj K)) :=
  sorry


/-- Extension-of-scalars unit
`RΓ(stage (n+1)) ⟶ RΓ(stage (n+1)) ⊗ 𝒪(stage n)` as `𝒪(stage (n+1))`-complexes. -/
def rGammaExtendUnitApp (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ)
    (K : QC (spfToGroupoids A structureHom)) :
    (chaoticRGamma.{u + 1, u, u}
        (affineStructureSheaf (spfToGroupoids A structureHom))
        (stageObj structureHom I hI (n + 1))).obj
      ((QC.inclusion (spfToGroupoids A structureHom)).obj K) ⟶
      (ModuleCat.derivedRestrictionOfScalars (stageCoeffHom structureHom I hI n)).obj
        ((chaoticRGamma.{u + 1, u, u}
              (affineStructureSheaf (spfToGroupoids A structureHom))
              (stageObj structureHom I hI (n + 1)) ⋙
            chaoticDerivedRestrict.{u + 1, u, u}
              (affineStructureSheaf (spfToGroupoids A structureHom))
              (stageHom structureHom I hI n)).obj
          ((QC.inclusion (spfToGroupoids A structureHom)).obj K)) :=
  (ModuleCat.derivedExtensionRestrictionAdjunction
      (stageCoeffHom structureHom I hI n)).unit.app
    ((chaoticRGamma.{u + 1, u, u}
        (affineStructureSheaf (spfToGroupoids A structureHom))
        (stageObj structureHom I hI (n + 1))).obj
      ((QC.inclusion (spfToGroupoids A structureHom)).obj K))


/-- Chaotic comparison `RΓ(stage (n+1)) ⊗ 𝒪(stage n) ⟶ RΓ(stage n)`. -/
def rGammaComparisonApp (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ)
    (K : QC (spfToGroupoids A structureHom)) :
    (chaoticRGamma.{u + 1, u, u}
          (affineStructureSheaf (spfToGroupoids A structureHom))
          (stageObj structureHom I hI (n + 1)) ⋙
        chaoticDerivedRestrict.{u + 1, u, u}
          (affineStructureSheaf (spfToGroupoids A structureHom))
          (stageHom structureHom I hI n)).obj
      ((QC.inclusion (spfToGroupoids A structureHom)).obj K) ⟶
      (chaoticRGamma.{u + 1, u, u}
          (affineStructureSheaf (spfToGroupoids A structureHom))
          (stageObj structureHom I hI n)).obj
        ((QC.inclusion (spfToGroupoids A structureHom)).obj K) :=
  (chaoticComparison.{u + 1, u, u}
      (affineStructureSheaf (spfToGroupoids A structureHom))
      (stageHom structureHom I hI n)).app
    ((QC.inclusion (spfToGroupoids A structureHom)).obj K)

/-- Restriction of scalars along `𝒪(n+1) → 𝒪(n)` is additive. -/
instance stageCoeffRestrict_additive (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    (ModuleCat.restrictScalars (stageCoeffHom structureHom I hI n)).Additive :=
  sorry

/-- Restriction of scalars along `𝒪(n+1) → 𝒪(n)` preserves finite limits. -/
instance stageCoeffRestrict_preservesFiniteLimits (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    PreservesFiniteLimits (ModuleCat.restrictScalars (stageCoeffHom structureHom I hI n)) :=
  sorry

/-- Restriction of scalars along `𝒪(n+1) → 𝒪(n)` preserves finite colimits. -/
instance stageCoeffRestrict_preservesFiniteColimits (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    PreservesFiniteColimits (ModuleCat.restrictScalars (stageCoeffHom structureHom I hI n)) :=
  sorry

/-- Bundled exact restriction of scalars along `𝒪(n+1) → 𝒪(n)`. -/
def stageCoeffRestrictExact (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    ModuleCat.{u + 1}
        ((affineStructureSheaf (spfToGroupoids A structureHom)).obj.obj
          (op (stageObj structureHom I hI n))) ⥤ₑ
      ModuleCat.{u + 1}
        ((affineStructureSheaf (spfToGroupoids A structureHom)).obj.obj
          (op (stageObj structureHom I hI (n + 1)))) :=
  ExactFunctor.of (ModuleCat.restrictScalars (stageCoeffHom structureHom I hI n))

/-- Bundled exact restriction of scalars from `𝒪(stage n)` to `A`. -/
def stageRestrictExact (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    ModuleCat.{u + 1}
        ((affineStructureSheaf (spfToGroupoids A structureHom)).obj.obj
          (op (stageObj structureHom I hI n))) ⥤ₑ
      ModuleCat.{u + 1} A :=
  ExactFunctor.of (stageRestrictScalars structureHom I hI n)

/-- The exact-functor isomorphism underlying `restrictScalarsComp'` at stage `n`. -/
def stageRestrictCompExactIso (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    (stageCoeffRestrictExact structureHom I hI n).comp
        (stageRestrictExact structureHom I hI (n + 1)) ≅
      stageRestrictExact structureHom I hI n :=
  { hom := homMk (ModuleCat.restrictScalarsComp' (stageRingHom structureHom I hI (n + 1))
        (stageCoeffHom structureHom I hI n) (stageRingHom structureHom I hI n)
        (stageRingHom_comp structureHom I hI n)).inv
    inv := homMk (ModuleCat.restrictScalarsComp' (stageRingHom structureHom I hI (n + 1))
        (stageCoeffHom structureHom I hI n) (stageRingHom structureHom I hI n)
        (stageRingHom_comp structureHom I hI n)).hom
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- Derived restriction along `𝒪(n+1) → 𝒪(n)` composed with restriction to `A` identifies
with restriction along `A → 𝒪(n)`. -/
def stageRestrictCompDerivedIso (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    (ModuleCat.derivedRestrictionOfScalars (stageCoeffHom structureHom I hI n)) ⋙
        stageDerivedRestrict structureHom I hI (n + 1) ≅
      stageDerivedRestrict structureHom I hI n :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
      (stageCoeffRestrictExact structureHom I hI n)
      (stageRestrictExact structureHom I hI (n + 1))).symm ≪≫
    ExactFunctor.MapDerivedCategory.mapIso
      (stageRestrictCompExactIso structureHom I hI n)


/-- The inverse-system transition: extension-of-scalars unit, then chaotic comparison, then
restriction of scalars to `A`. -/
def rGammaTransitionApp (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ)
    (K : QC (spfToGroupoids A structureHom)) :
    (rGammaStage structureHom I hI (n + 1)).obj K ⟶
      (rGammaStage structureHom I hI n).obj K :=
  (stageDerivedRestrict structureHom I hI (n + 1)).map
      (rGammaExtendUnitApp structureHom I hI n K) ≫
    (stageRestrictCompDerivedIso structureHom I hI n).hom.app _ ≫
      (stageDerivedRestrict structureHom I hI n).map
        (rGammaComparisonApp structureHom I hI n K)

/-- `rGammaTransitionApp n` is restriction of scalars of the extension unit followed by the
chaotic comparison. -/
theorem rGammaTransitionApp_eq (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ)
    (K : QC (spfToGroupoids A structureHom)) :
    rGammaTransitionApp structureHom I hI n K =
      (stageDerivedRestrict structureHom I hI (n + 1)).map
          (rGammaExtendUnitApp structureHom I hI n K) ≫
        (stageRestrictCompDerivedIso structureHom I hI n).hom.app _ ≫
          (stageDerivedRestrict structureHom I hI n).map
            (rGammaComparisonApp structureHom I hI n K) :=
  sorry

/-- Stagewise derived sections of a quasi-coherent object, as a family indexed by `ℕ`. -/
def rGammaStageObj (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (K : QC (spfToGroupoids A structureHom)) (n : ℕ) :
    DerivedCategory (ModuleCat.{u + 1} A) :=
  (rGammaStage structureHom I hI n).obj K

/-- `rGammaStageObj` is evaluation of `rGammaStage`. -/
theorem rGammaStageObj_eq (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (K : QC (spfToGroupoids A structureHom)) (n : ℕ) :
    rGammaStageObj structureHom I hI K n = (rGammaStage structureHom I hI n).obj K :=
  sorry

/-- The successor transition as a map of the `ℕ`-indexed family `rGammaStageObj`. -/
def rGammaTransition (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (K : QC (spfToGroupoids A structureHom)) (n : ℕ) :
    rGammaStageObj structureHom I hI K (n + 1) ⟶ rGammaStageObj structureHom I hI K n :=
  rGammaTransitionApp structureHom I hI n K

/-- The inverse system of infinitesimal derived sections of a quasi-coherent object. -/
def rGammaSystem (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (K : QC (spfToGroupoids A structureHom)) :
    SequentialInverseSystem (DerivedCategory (ModuleCat.{u + 1} A)) :=
  Functor.ofOpSequence (rGammaTransition structureHom I hI K)

/-- Evaluating `rGammaSystem K` at `n` recovers `rGammaStage n`. -/
theorem rGammaSystem_obj (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (K : QC (spfToGroupoids A structureHom)) (n : ℕ) :
    (rGammaSystem structureHom I hI K).obj (op n) =
      (rGammaStage structureHom I hI n).obj K :=
  sorry

/-- The inverse system of infinitesimal derived sections, as a functor on `QC(Spf(A))`. -/
def rGammaSystemFunctor (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    QC (spfToGroupoids A structureHom) ⥤
      SequentialInverseSystem (DerivedCategory (ModuleCat.{u + 1} A)) where
  obj := rGammaSystem structureHom I hI
  map {K L} f :=
    NatTrans.ofOpSequence (fun n ↦ (rGammaStage structureHom I hI n).map f) sorry
  map_id := sorry
  map_comp := sorry

/-- Objectwise, `rGammaSystemFunctor` is `rGammaSystem`. -/
theorem rGammaSystemFunctor_obj (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (K : QC (spfToGroupoids A structureHom)) :
    (rGammaSystemFunctor structureHom I hI).obj K =
      rGammaSystem structureHom I hI K :=
  sorry


/-- Modules on the chaotic affine site of `Spf(A)`. -/
abbrev spfAffineModules (structureHom : Spec (.of A) ⟶ S) :=
  ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
    (⊥ : GrothendieckTopology (affineSite (spfToGroupoids A structureHom)))
    (affineStructureSheaf (spfToGroupoids A structureHom))

/-- `spfAffineModules structureHom` is the chaotic module category on `𝒳_affine`. -/
theorem spfAffineModules_eq (structureHom : Spec (.of A) ⟶ S) :
    spfAffineModules structureHom =
      ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
        (⊥ : GrothendieckTopology (affineSite (spfToGroupoids A structureHom)))
        (affineStructureSheaf (spfToGroupoids A structureHom)) :=
  sorry

/-- The canonical standard derived-category structure on chaotic affine modules of `Spf(A)`. -/
instance hasDerivedCategory_spfAffineModules (structureHom : Spec (.of A) ⟶ S) :
    HasDerivedCategory (spfAffineModules structureHom) :=
  RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1, u + 1, u, u + 1}
    (RingedSite.ofCommRingSheaf ⊥
      (affineStructureSheaf (spfToGroupoids A structureHom)))

/-- The cochain-complex representative of a quasi-coherent derived module on `Spf(A)`,
taken from the standard localization wrapping. -/
def asSheafComplex (structureHom : Spec (.of A) ⟶ S)
    (K : QC (spfToGroupoids A structureHom)) :
    CochainComplex (spfAffineModules structureHom) ℤ :=
  ((QC.inclusion (spfToGroupoids A structureHom)).obj K).as.obj

/-- `asSheafComplex` is the underlying cochain complex of the included derived module. -/
theorem asSheafComplex_eq (structureHom : Spec (.of A) ⟶ S)
    (K : QC (spfToGroupoids A structureHom)) :
    asSheafComplex structureHom K =
      ((QC.inclusion (spfToGroupoids A structureHom)).obj K).as.obj :=
  sorry

/-- Universe-pinned evaluation of affine modules at an infinitesimal stage. -/
abbrev stageEvaluation (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    spfAffineModules structureHom ⥤
      ModuleCat.{u + 1}
        ((affineStructureSheaf (spfToGroupoids A structureHom)).obj.obj
          (op (stageObj structureHom I hI n))) :=
  SheafOfModules.RingedSite.BaseChange.evaluation.{u + 1, u, u + 1, u + 1}
    (affineStructureSheaf (spfToGroupoids A structureHom))
    (stageObj structureHom I hI n)

/-- `stageEvaluation n` is universe-pinned chaotic base-change evaluation at `stage n`. -/
theorem stageEvaluation_eq (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    stageEvaluation structureHom I hI n =
      SheafOfModules.RingedSite.BaseChange.evaluation.{u + 1, u, u + 1, u + 1}
        (affineStructureSheaf (spfToGroupoids A structureHom))
        (stageObj structureHom I hI n) :=
  sorry

/-- Chaotic base-change evaluation at an infinitesimal stage is additive. -/
instance stageEvaluation_additive (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    (stageEvaluation structureHom I hI n).Additive :=
  sorry

/-- Chaotic base-change evaluation at an infinitesimal stage preserves zero morphisms. -/
instance stageBaseChangeEvaluation_preservesZeroMorphisms (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    (stageEvaluation structureHom I hI n).PreservesZeroMorphisms :=
  sorry

/-- Chaotic evaluation at an infinitesimal stage preserves zero morphisms. -/
instance chaoticSections_preservesZeroMorphisms (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    (chaoticSections.{u + 1, u, u}
        (affineStructureSheaf (spfToGroupoids A structureHom))
        (stageObj structureHom I hI n)).PreservesZeroMorphisms :=
  sorry

/-- Extension of scalars along `𝒪(stage (n+1)) → 𝒪(stage n)` is additive. -/
instance stageExtendScalars_additive (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (stageCoeffHom structureHom I hI n)).Additive :=
  sorry

/-- Extension of scalars along `𝒪(stage (n+1)) → 𝒪(stage n)` preserves zero morphisms. -/
instance stageExtendScalars_preservesZeroMorphisms (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (stageCoeffHom structureHom I hI n)).PreservesZeroMorphisms :=
  sorry

/-- Evaluation at stage `n+1`, followed by extension of scalars to `𝒪(stage n)`. -/
def stageExtendEvaluate (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    spfAffineModules structureHom ⥤
      ModuleCat.{u + 1}
        ((affineStructureSheaf (spfToGroupoids A structureHom)).obj.obj
          (op (stageObj structureHom I hI n))) :=
  stageEvaluation structureHom I hI (n + 1) ⋙
    ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (stageCoeffHom structureHom I hI n)

/-- `stageExtendEvaluate n` is evaluation at stage `n+1` followed by extension of scalars. -/
theorem stageExtendEvaluate_eq (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    stageExtendEvaluate structureHom I hI n =
      stageEvaluation structureHom I hI (n + 1) ⋙
        ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
          (stageCoeffHom structureHom I hI n) :=
  sorry

/-- Evaluation-then-extend identifies with the sheaf-level base-change functor, by associativity
of functor composition. -/
def stageExtendEvaluateIso (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    stageExtendEvaluate structureHom I hI n ≅
      SheafOfModules.RingedSite.BaseChange.functor.{u + 1, u, u + 1, u + 1}
        (affineStructureSheaf (spfToGroupoids A structureHom))
        (stageHom structureHom I hI n) :=
  Functor.associator
    (SheafOfModules.RingedSite.BaseChange.forget.{u + 1, u, u + 1, u + 1}
      (affineStructureSheaf (spfToGroupoids A structureHom)))
    (PresheafOfModules.BaseChange.evaluation.{u + 1, u, u + 1, u + 1}
      (affineStructureSheaf (spfToGroupoids A structureHom)).obj
      (op (stageObj structureHom I hI (n + 1))))
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (stageCoeffHom structureHom I hI n))

/-- The sheaf-level base-change functor at an infinitesimal stage is additive. -/
instance stageBaseChange_additive (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    (SheafOfModules.RingedSite.BaseChange.functor.{u + 1, u, u + 1, u + 1}
        (affineStructureSheaf (spfToGroupoids A structureHom))
        (stageHom structureHom I hI n)).Additive :=
  sorry

/-- The chaotic base-change functor at an infinitesimal stage preserves zero morphisms. -/
instance stageBaseChange_preservesZeroMorphisms (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    (SheafOfModules.RingedSite.BaseChange.functor.{u + 1, u, u + 1, u + 1}
        (affineStructureSheaf (spfToGroupoids A structureHom))
        (stageHom structureHom I hI n)).PreservesZeroMorphisms :=
  sorry

/-- Evaluation-then-extend at an infinitesimal stage is additive. -/
instance stageExtendEvaluate_additive (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    (stageExtendEvaluate structureHom I hI n).Additive :=
  sorry

/-- Restriction of scalars along `𝒪(stage (n+1)) → 𝒪(stage n)` preserves zero morphisms. -/
instance stageCoeffRestrict_preservesZeroMorphisms (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    (ModuleCat.restrictScalars.{u + 1} (stageCoeffHom structureHom I hI n)).PreservesZeroMorphisms :=
  sorry

/-- Restriction of scalars from `𝒪(stage n)` to `A` preserves zero morphisms. -/
instance stageRestrictScalars_preservesZeroMorphisms (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    (stageRestrictScalars structureHom I hI n).PreservesZeroMorphisms :=
  sorry

/-- Chaotic evaluation at `stage n`, as a functor on cochain complexes of affine modules. -/
def stageEvaluateComplex (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    CochainComplex (spfAffineModules structureHom) ℤ ⥤
      CochainComplex
        (ModuleCat.{u + 1}
          ((affineStructureSheaf (spfToGroupoids A structureHom)).obj.obj
            (op (stageObj structureHom I hI n)))) ℤ :=
  (stageEvaluation structureHom I hI n).mapHomologicalComplex (ComplexShape.up ℤ)

/-- `stageEvaluateComplex n` is base-change evaluation at `stage n` on cochain complexes. -/
theorem stageEvaluateComplex_eq (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    stageEvaluateComplex structureHom I hI n =
      (stageEvaluation structureHom I hI n).mapHomologicalComplex (ComplexShape.up ℤ) :=
  sorry

/-- Infinitesimal sections at stage `n`, restricted to cochain complexes of `A`-modules. -/
def stageComplexFunctor (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    CochainComplex (spfAffineModules structureHom) ℤ ⥤
      CochainComplex (ModuleCat.{u + 1} A) ℤ :=
  stageEvaluateComplex structureHom I hI n ⋙
    (stageRestrictScalars structureHom I hI n).mapHomologicalComplex (ComplexShape.up ℤ)

/-- `stageComplexFunctor n` is evaluation at stage `n` followed by restriction of scalars to `A`. -/
theorem stageComplexFunctor_eq (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    stageComplexFunctor structureHom I hI n =
      stageEvaluateComplex structureHom I hI n ⋙
        (stageRestrictScalars structureHom I hI n).mapHomologicalComplex (ComplexShape.up ℤ) :=
  sorry

/-- Extension-restriction unit at stage `n+1`, as a morphism of cochain complexes. -/
def stageExtendUnitComplex (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ)
    (S : CochainComplex (spfAffineModules structureHom) ℤ) :
    (stageEvaluateComplex structureHom I hI (n + 1)).obj S ⟶
      ((ModuleCat.restrictScalars.{u + 1} (stageCoeffHom structureHom I hI n)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
              (stageCoeffHom structureHom I hI n)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          ((stageEvaluateComplex structureHom I hI (n + 1)).obj S)) :=
  (Adjunction.mapHomologicalComplexAdjunction
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1}
        (stageCoeffHom structureHom I hI n))
      (ComplexShape.up ℤ)).unit.app
    ((stageEvaluateComplex structureHom I hI (n + 1)).obj S)

/-- Chaotic base-change comparison at stage `n`, as a morphism of cochain complexes. -/
def stageComparisonComplex (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ)
    (S : CochainComplex (spfAffineModules structureHom) ℤ) :
    ((stageExtendEvaluate structureHom I hI n).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj S ⟶
      (stageEvaluateComplex structureHom I hI n).obj S :=
  (NatTrans.mapHomologicalComplex
      ((stageExtendEvaluateIso structureHom I hI n).hom ≫
        SheafOfModules.RingedSite.BaseChange.natTrans.{u + 1, u, u + 1, u + 1}
          (affineStructureSheaf (spfToGroupoids A structureHom))
          (stageHom structureHom I hI n))
      (ComplexShape.up ℤ)).app S

/-- Restriction of scalars along `A → 𝒪(n)` identifies with restriction along
`A → 𝒪(n+1) → 𝒪(n)`, on cochain complexes. -/
def stageRestrictCompComplexIso (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    (ModuleCat.restrictScalars.{u + 1} (stageCoeffHom structureHom I hI n) ⋙
        stageRestrictScalars structureHom I hI (n + 1)).mapHomologicalComplex
      (ComplexShape.up ℤ) ≅
      (stageRestrictScalars structureHom I hI n).mapHomologicalComplex (ComplexShape.up ℤ) :=
  (NatIso.mapHomologicalComplex
      (ModuleCat.restrictScalarsComp'
        (stageRingHom structureHom I hI (n + 1)) (stageCoeffHom structureHom I hI n)
        (stageRingHom structureHom I hI n) (stageRingHom_comp structureHom I hI n)).symm
      (ComplexShape.up ℤ))

/-- Infinitesimal stage complexes of an affine-module complex, as an `ℕ`-indexed family. -/
def stageComplexObj (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (S : CochainComplex (spfAffineModules structureHom) ℤ) (n : ℕ) :
    CochainComplex (ModuleCat.{u + 1} A) ℤ :=
  (stageComplexFunctor structureHom I hI n).obj S

/-- `stageComplexObj` is evaluation of `stageComplexFunctor`. -/
theorem stageComplexObj_eq (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (S : CochainComplex (spfAffineModules structureHom) ℤ) (n : ℕ) :
    stageComplexObj structureHom I hI S n =
      (stageComplexFunctor structureHom I hI n).obj S :=
  sorry

/-- The inverse-system transition on stage complexes: extension unit, chaotic comparison, then
restriction of scalars to `A`. -/
def stageComplexTransition (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (S : CochainComplex (spfAffineModules structureHom) ℤ) (n : ℕ) :
    stageComplexObj structureHom I hI S (n + 1) ⟶
      stageComplexObj structureHom I hI S n :=
  ((stageRestrictScalars structureHom I hI (n + 1)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
      (stageExtendUnitComplex structureHom I hI n S) ≫
    (stageRestrictCompComplexIso structureHom I hI n).hom.app _ ≫
      ((stageRestrictScalars structureHom I hI n).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (stageComparisonComplex structureHom I hI n S)

/-- The inverse system of infinitesimal stage complexes of a cochain complex of affine modules. -/
def rGammaComplexSystem (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (S : CochainComplex (spfAffineModules structureHom) ℤ) :
    SequentialInverseSystem (CochainComplex (ModuleCat.{u + 1} A) ℤ) :=
  Functor.ofOpSequence (stageComplexTransition structureHom I hI S)

/-- Evaluating `rGammaComplexSystem S` at `n` recovers `stageComplexFunctor n`. -/
theorem rGammaComplexSystem_obj (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (S : CochainComplex (spfAffineModules structureHom) ℤ) (n : ℕ) :
    (rGammaComplexSystem structureHom I hI S).obj (op n) =
      (stageComplexFunctor structureHom I hI n).obj S :=
  sorry

/-- A morphism of affine-module complexes induces a morphism of infinitesimal stage systems. -/
def rGammaComplexSystemMap (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    {S T : CochainComplex (spfAffineModules structureHom) ℤ} (f : S ⟶ T) :
    rGammaComplexSystem structureHom I hI S ⟶ rGammaComplexSystem structureHom I hI T :=
  NatTrans.ofOpSequence
    (fun n ↦ (stageComplexFunctor structureHom I hI n).map f) sorry

/-- The product of infinitesimal stage complexes exists because products of `A`-modules are
computed termwise on cochain complexes. -/
instance hasProduct_rGammaComplexSystem (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (S : CochainComplex (spfAffineModules structureHom) ℤ) :
    HasProduct (rGammaComplexSystem structureHom I hI S).family :=
  inferInstance

/-- The mapping cocone of the Milnor difference of the product of infinitesimal stage complexes. -/
def holimComplex (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (S : CochainComplex (spfAffineModules structureHom) ℤ) :
    CochainComplex (ModuleCat.{u + 1} A) ℤ :=
  CochainComplex.mappingCocone
    (rGammaComplexSystem structureHom I hI S).milnorDifferenceMap

/-- `holimComplex S` is the mapping cocone of the Milnor difference of `rGammaComplexSystem S`. -/
theorem holimComplex_eq (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (S : CochainComplex (spfAffineModules structureHom) ℤ) :
    holimComplex structureHom I hI S =
      CochainComplex.mappingCocone
        (rGammaComplexSystem structureHom I hI S).milnorDifferenceMap :=
  sorry

/-- The cochain-level Milnor homotopy limit of infinitesimal stage complexes. -/
def holimComplexFunctor (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    CochainComplex (spfAffineModules structureHom) ℤ ⥤
      CochainComplex (ModuleCat.{u + 1} A) ℤ where
  obj S := holimComplex structureHom I hI S
  map {S T} f :=
    (shiftFunctor (CochainComplex (ModuleCat.{u + 1} A) ℤ) (-1 : ℤ)).map
      (CochainComplex.mappingCone.map
        (rGammaComplexSystem structureHom I hI S).milnorDifferenceMap
        (rGammaComplexSystem structureHom I hI T).milnorDifferenceMap
        (SequentialInverseSystem.productMap (rGammaComplexSystemMap structureHom I hI f))
        (SequentialInverseSystem.productMap (rGammaComplexSystemMap structureHom I hI f))
        (SequentialInverseSystem.milnorDifferenceMap_naturality
          (rGammaComplexSystemMap structureHom I hI f)))
  map_id := sorry
  map_comp := sorry

/-- Objectwise, `holimComplexFunctor` is `holimComplex`. -/
theorem holimComplexFunctor_obj (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (S : CochainComplex (spfAffineModules structureHom) ℤ) :
    (holimComplexFunctor structureHom I hI).obj S =
      holimComplex structureHom I hI S :=
  sorry

/-- The Milnor homotopy limit of infinitesimal stage complexes, as an object of `D(A)`. -/
def holimFromComplex (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    CochainComplex (spfAffineModules structureHom) ℤ ⥤
      DerivedCategory (ModuleCat.{u + 1} A) :=
  holimComplexFunctor structureHom I hI ⋙ DerivedCategory.Q

/-- Objectwise, `holimFromComplex` is `Q` of `holimComplex`. -/
theorem holimFromComplex_obj (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (S : CochainComplex (spfAffineModules structureHom) ℤ) :
    (holimFromComplex structureHom I hI).obj S =
      DerivedCategory.Q.obj (holimComplex structureHom I hI S) :=
  sorry

/-- Quasi-isomorphisms of affine-module complexes remain invertible after taking the Milnor
homotopy limit of infinitesimal stages. -/
theorem holimFromComplex_inverts_quasiIso (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    (HomologicalComplex.quasiIso (spfAffineModules structureHom) (ComplexShape.up ℤ)).IsInvertedBy
      (holimFromComplex structureHom I hI) :=
  sorry

/-- The Milnor mapping-cocone image of a quasi-isomorphism of affine-module complexes is a
quasi-isomorphism of `A`-complexes. -/
theorem holimComplexFunctor_map_quasiIso (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    {S T : CochainComplex (spfAffineModules structureHom) ℤ} (f : S ⟶ T)
    (hf : QuasiIso f) :
    QuasiIso ((holimComplexFunctor structureHom I hI).map f) :=
  sorry

/-- The image of a generating arrow of the affine-module localization quiver under the
explicit Milnor mapping cocone. Cochain maps are sent to `holimComplexFunctor.map`, and
formal inverses of quasi-isomorphisms are sent to formal inverses of those Milnor images. -/
def holimLocQuiverMap (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    {X Y : Construction.LocQuiver
      (HomologicalComplex.quasiIso (spfAffineModules structureHom) (ComplexShape.up ℤ))}
    (e : X ⟶ Y) :
    DerivedCategory.Q.obj (holimComplex structureHom I hI X.obj) ⟶
      DerivedCategory.Q.obj (holimComplex structureHom I hI Y.obj) :=
  match e with
  | Sum.inl g =>
      DerivedCategory.Q.map ((holimComplexFunctor structureHom I hI).map g)
  | Sum.inr ⟨w, hw⟩ =>
      Construction.wInv ((holimComplexFunctor structureHom I hI).map w)
        (holimComplexFunctor_map_quasiIso structureHom I hI w hw)

/-- The image of a path of affine-module localization arrows under the explicit Milnor
mapping cocone. -/
def holimLocPathMap (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    {X : Construction.LocQuiver
      (HomologicalComplex.quasiIso (spfAffineModules structureHom) (ComplexShape.up ℤ))} :
    ∀ {Y : Construction.LocQuiver
        (HomologicalComplex.quasiIso (spfAffineModules structureHom) (ComplexShape.up ℤ))},
      Quiver.Path X Y →
        (DerivedCategory.Q.obj (holimComplex structureHom I hI X.obj) ⟶
          DerivedCategory.Q.obj (holimComplex structureHom I hI Y.obj))
  | _, Quiver.Path.nil => 𝟙 _
  | _, Quiver.Path.cons p e =>
      holimLocPathMap structureHom I hI p ≫ holimLocQuiverMap structureHom I hI e

/-- Cochain maps are sent by `holimLocQuiverMap` to `Q` of the explicit Milnor mapping-cocone
map. -/
theorem holimLocQuiverMap_inl (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    {X Y : Construction.LocQuiver
      (HomologicalComplex.quasiIso (spfAffineModules structureHom) (ComplexShape.up ℤ))}
    (g : X.obj ⟶ Y.obj) :
    holimLocQuiverMap structureHom I hI (Sum.inl g) =
      DerivedCategory.Q.map ((holimComplexFunctor structureHom I hI).map g) :=
  sorry

/-- The empty localization path is sent to the identity of the Milnor mapping cocone. -/
theorem holimLocPathMap_nil (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    {X : Construction.LocQuiver
      (HomologicalComplex.quasiIso (spfAffineModules structureHom) (ComplexShape.up ℤ))} :
    holimLocPathMap structureHom I hI (Quiver.Path.nil : Quiver.Path X X) = 𝟙 _ :=
  sorry

/-- The localization-path representative of a morphism of quasi-coherent derived modules. -/
def asSheafComplexMap (structureHom : Spec (.of A) ⟶ S)
    {K L : QC (spfToGroupoids A structureHom)} (f : K ⟶ L) :
    ((QC.inclusion (spfToGroupoids A structureHom)).obj K).as ⟶
      ((QC.inclusion (spfToGroupoids A structureHom)).obj L).as :=
  Quot.out ((QC.inclusion (spfToGroupoids A structureHom)).map f)

/-- `asSheafComplexMap f` is the chosen path representative of the included derived morphism. -/
theorem asSheafComplexMap_eq (structureHom : Spec (.of A) ⟶ S)
    {K L : QC (spfToGroupoids A structureHom)} (f : K ⟶ L) :
    asSheafComplexMap structureHom f =
      Quot.out ((QC.inclusion (spfToGroupoids A structureHom)).map f) :=
  sorry

/-- The Milnor homotopy limit, descended from affine-module complexes to `D` of chaotic
affine modules. Objects are `Q` of the explicit mapping cocone, and morphisms are the
images of localization-path representatives under `holimComplexFunctor`. -/
def holimFromSheaves (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    DerivedCategory (spfAffineModules structureHom) ⥤
      DerivedCategory (ModuleCat.{u + 1} A) where
  obj K := DerivedCategory.Q.obj (holimComplex structureHom I hI K.as.obj)
  map {K L} f := holimLocPathMap structureHom I hI (Quot.out f)
  map_id := sorry
  map_comp := sorry

/-- Objectwise, `holimFromSheaves` is `Q` of the explicit Milnor mapping cocone. -/
theorem holimFromSheaves_obj (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (K : DerivedCategory (spfAffineModules structureHom)) :
    (holimFromSheaves structureHom I hI).obj K =
      DerivedCategory.Q.obj (holimComplex structureHom I hI K.as.obj) :=
  sorry

/-- The derived limit of infinitesimal sections, in the universe of chaotic derived sections.
Objects are `Q` of the explicit Milnor mapping cocone of `asSheafComplex`, and morphisms are
`holimComplexFunctor.map` of the localization-path representative `asSheafComplexMap`. -/
def derivedLimitLarge (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    QC (spfToGroupoids A structureHom) ⥤ DerivedCategory (ModuleCat.{u + 1} A) where
  obj K :=
    DerivedCategory.Q.obj (holimComplex structureHom I hI (asSheafComplex structureHom K))
  map {K L} f := holimLocPathMap structureHom I hI (asSheafComplexMap structureHom f)
  map_id := sorry
  map_comp := sorry

/-- Objectwise, `derivedLimitLarge` is the Milnor homotopy limit of the stage complexes of `K`. -/
theorem derivedLimitLarge_obj (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (K : QC (spfToGroupoids A structureHom)) :
    (derivedLimitLarge structureHom I hI).obj K =
      DerivedCategory.Q.obj
        (holimComplex structureHom I hI (asSheafComplex structureHom K)) :=
  sorry

/-- The large derived limit is a sequential homotopy limit of the infinitesimal `RΓ` tower. -/
theorem derivedLimitLarge_isOf (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (K : QC (spfToGroupoids A structureHom)) :
    HomotopyLimit.IsOf (rGammaSystem structureHom I hI K)
      ((derivedLimitLarge structureHom I hI).obj K) :=
  sorry

/-- The holimit of the infinitesimal `RΓ` tower is derived complete with respect to `I`. -/
theorem derivedLimitLarge_isDerivedComplete [IsNoetherianRing A]
    (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (K : QC (spfToGroupoids A structureHom)) :
    DerivedCategory.IsDerivedCompleteWithRespectTo.{u, u + 1}
      ((derivedLimitLarge structureHom I hI).obj K) I :=
  sorry

/-- Canonical comparison functor `QC(Spf(A)) ⥤ D_comp(A, I)`. -/
def toDerivedComplete [IsNoetherianRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    QC (spfToGroupoids A structureHom) ⥤
      (DerivedCategory.derivedCompleteObjectProperty.{u, u + 1} I).FullSubcategory :=
  (DerivedCategory.derivedCompleteObjectProperty.{u, u + 1} I).lift
    (derivedLimitLarge structureHom I hI)
    (derivedLimitLarge_isDerivedComplete structureHom I hI)

/-- The underlying object of `toDerivedComplete` is the Milnor homotopy limit of the
infinitesimal section tower. -/
theorem toDerivedComplete_obj [IsNoetherianRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (K : QC (spfToGroupoids A structureHom)) :
    ((DerivedCategory.derivedCompleteObjectProperty.{u, u + 1} I).ι).obj
        ((toDerivedComplete structureHom I hI).obj K) =
      (derivedLimitLarge structureHom I hI).obj K :=
  sorry

end AlgebraicGeometry.GroupoidsOver

