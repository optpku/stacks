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
public import ReasLib.RingTheory.Topology.Adic.Powers
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Derived.QuasiCoherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Sections.BaseChange
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalSpectrum

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

/-- The weak ideal of definition `I^{n+1}` indexing the `n`th infinitesimal stage. -/
def powerStage (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (n : ℕ) : WeakIdealOfDefinition A :=
  WeakIdealOfDefinition.of (I ^ (n + 1)) (hI.isWeak_pow n)

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
  rfl

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
  rfl

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
  rfl



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
  rfl


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
  rfl

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
abbrev stageRestrictScalars (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    ModuleCat.{u + 1}
        ((affineStructureSheaf (spfToGroupoids A structureHom)).obj.obj
          (op (stageObj structureHom I hI n))) ⥤
      ModuleCat.{u + 1} A :=
  ModuleCat.restrictScalars (stageRingHom structureHom I hI n)

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
  rfl


/-- Extension-of-scalars unit
`RΓ(stage (n+1)) ⟶ RΓ(stage (n+1)) ⊗ 𝒪(stage n)` as `𝒪(stage (n+1))`-complexes. -/
def rGammaExtendUnitApp (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ)
    (K : QC (spfToGroupoids A structureHom)) :
    (chaoticRGamma.{u + 1, u, u}
        (affineStructureSheaf (spfToGroupoids A structureHom))
        (stageObj structureHom I hI (n + 1))).obj
      ((QC.inclusion (spfToGroupoids A structureHom)).obj K) ⟶
      (ModuleCat.derivedRestrictionOfScalars.{u + 1, u + 1} (stageCoeffHom structureHom I hI n)).obj
        ((chaoticRGamma.{u + 1, u, u}
              (affineStructureSheaf (spfToGroupoids A structureHom))
              (stageObj structureHom I hI (n + 1)) ⋙
            chaoticDerivedRestrict.{u + 1, u, u}
              (affineStructureSheaf (spfToGroupoids A structureHom))
              (stageHom structureHom I hI n)).obj
          ((QC.inclusion (spfToGroupoids A structureHom)).obj K)) :=
  (ModuleCat.derivedExtensionRestrictionAdjunction.{u + 1, u + 1}
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
      stageRestrictExact structureHom I hI n := by
  let f : (stageCoeffRestrictExact structureHom I hI n).comp
      (stageRestrictExact structureHom I hI (n + 1)) ⟶ stageRestrictExact structureHom I hI n :=
    homMk (ModuleCat.restrictScalarsComp' (stageRingHom structureHom I hI (n + 1))
      (stageCoeffHom structureHom I hI n) (stageRingHom structureHom I hI n)
      (stageRingHom_comp structureHom I hI n)).inv
  let g : stageRestrictExact structureHom I hI n ⟶ (stageCoeffRestrictExact structureHom I hI n).comp
      (stageRestrictExact structureHom I hI (n + 1)) :=
    homMk (ModuleCat.restrictScalarsComp' (stageRingHom structureHom I hI (n + 1))
      (stageCoeffHom structureHom I hI n) (stageRingHom structureHom I hI n)
      (stageRingHom_comp structureHom I hI n)).hom
  have laws : f ≫ g = 𝟙 _ ∧ g ≫ f = 𝟙 _ := sorry
  exact ⟨f, g, laws.1, laws.2⟩

/-- Derived restriction along `𝒪(n+1) → 𝒪(n)` composed with restriction to `A` identifies
with restriction along `A → 𝒪(n)`. -/
def stageRestrictCompDerivedIso (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (n : ℕ) :
    (ModuleCat.derivedRestrictionOfScalars.{u + 1, u + 1} (stageCoeffHom structureHom I hI n)) ⋙
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
  rfl

/-- The inverse system of infinitesimal derived sections of a quasi-coherent object. -/
def rGammaSystem (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (K : QC (spfToGroupoids A structureHom)) :
    SequentialInverseSystem (DerivedCategory (ModuleCat.{u + 1} A)) :=
  Functor.ofOpSequence (X := fun n ↦ (rGammaStage structureHom I hI n).obj K)
    (fun n ↦ rGammaTransitionApp structureHom I hI n K)

/-- Evaluating `rGammaSystem K` at `n` recovers `rGammaStage n`. -/
theorem rGammaSystem_obj (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (K : QC (spfToGroupoids A structureHom)) (n : ℕ) :
    (rGammaSystem structureHom I hI K).obj (op n) =
      (rGammaStage structureHom I hI n).obj K :=
  rfl

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
  rfl

/-- The canonical standard derived-category structure on chaotic affine modules of `Spf(A)`. -/
instance hasDerivedCategory_spfAffineModules (structureHom : Spec (.of A) ⟶ S) :
    HasDerivedCategory (spfAffineModules structureHom) :=
  RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1, u + 1, u, u + 1}
    (RingedSite.ofCommRingSheaf ⊥
      (affineStructureSheaf (spfToGroupoids A structureHom)))

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
  rfl

/-- Evaluation at stage `n+1`, followed by extension of scalars to `𝒪(stage n)`. -/
abbrev stageExtendEvaluate (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
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
  rfl

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
  rfl

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
  rfl

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
  rfl

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
  rfl

/-- A morphism of affine-module complexes induces a morphism of infinitesimal stage systems. -/
def rGammaComplexSystemMap (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    {S T : CochainComplex (spfAffineModules structureHom) ℤ} (f : S ⟶ T) :
    rGammaComplexSystem structureHom I hI S ⟶ rGammaComplexSystem structureHom I hI T :=
  NatTrans.ofOpSequence
    (fun n ↦ (stageComplexFunctor structureHom I hI n).map f) sorry

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
  rfl

/-- The cochain-level Milnor homotopy limit of infinitesimal stage complexes. -/
def holimComplexFunctor (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    CochainComplex (spfAffineModules structureHom) ℤ ⥤
      CochainComplex (ModuleCat.{u + 1} A) ℤ := by
  let obj := holimComplex structureHom I hI
  let map : ∀ {S T : CochainComplex (spfAffineModules structureHom) ℤ},
      (S ⟶ T) → (obj S ⟶ obj T) := fun {S T} f ↦
    (shiftFunctor (CochainComplex (ModuleCat.{u + 1} A) ℤ) (-1 : ℤ)).map
      (CochainComplex.mappingCone.map
        (rGammaComplexSystem structureHom I hI S).milnorDifferenceMap
        (rGammaComplexSystem structureHom I hI T).milnorDifferenceMap
        (SequentialInverseSystem.productMap (rGammaComplexSystemMap structureHom I hI f))
        (SequentialInverseSystem.productMap (rGammaComplexSystemMap structureHom I hI f))
        (SequentialInverseSystem.milnorDifferenceMap_naturality
          (rGammaComplexSystemMap structureHom I hI f)))
  have laws : (∀ S, map (𝟙 S) = 𝟙 (obj S)) ∧
      (∀ {S T U} (f : S ⟶ T) (g : T ⟶ U), map (f ≫ g) = map f ≫ map g) := sorry
  exact { obj := obj, map := map, map_id := laws.1, map_comp := laws.2 }

/-- Objectwise, `holimComplexFunctor` is `holimComplex`. -/
theorem holimComplexFunctor_obj (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (S : CochainComplex (spfAffineModules structureHom) ℤ) :
    (holimComplexFunctor structureHom I hI).obj S =
      holimComplex structureHom I hI S :=
  rfl

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
  rfl

/-- Quasi-isomorphisms of affine-module complexes remain invertible after taking the Milnor
homotopy limit of infinitesimal stages. -/
theorem holimFromComplex_inverts_quasiIso (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    (HomologicalComplex.quasiIso (spfAffineModules structureHom) (ComplexShape.up ℤ)).IsInvertedBy
      (holimFromComplex structureHom I hI) :=
  sorry

/-- The Milnor homotopy limit descended from affine-module complexes by localization. -/
def holimFromSheaves (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    DerivedCategory (spfAffineModules structureHom) ⥤
      DerivedCategory (ModuleCat.{u + 1} A) :=
  Localization.lift (holimFromComplex structureHom I hI)
    (holimFromComplex_inverts_quasiIso structureHom I hI) DerivedCategory.Q

/-- The descended Milnor functor agrees with the cochain construction after localization. -/
def holimFromSheavesFactors (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    DerivedCategory.Q ⋙ holimFromSheaves structureHom I hI ≅
      holimFromComplex structureHom I hI :=
  Localization.fac (holimFromComplex structureHom I hI)
    (holimFromComplex_inverts_quasiIso structureHom I hI) DerivedCategory.Q

/-- The descended Milnor homotopy limit restricted to quasi-coherent derived objects. -/
def derivedLimitLarge (structureHom : Spec (.of A) ⟶ S) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    QC (spfToGroupoids A structureHom) ⥤ DerivedCategory (ModuleCat.{u + 1} A) :=
  QC.inclusion (spfToGroupoids A structureHom) ⋙ holimFromSheaves structureHom I hI

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
  rfl

end AlgebraicGeometry.GroupoidsOver

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Let `S` be a scheme and let `A` be an adic Noetherian topological
`S`-algebra with ideal of definition `I`. Write `X = Spf(A)` and let `𝒳` be the category
fibred in sets associated to the fppf functor `X`. Then `QC(𝒳)` is canonically equivalent
to the category `D_comp(A, I)` of objects of `D(A)` which are derived complete with
respect to `I`. -/
@[stacks 0H0L, instance]
instance toDerivedComplete_isEquivalence
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsNoetherianRing A]
    [TopologicalRing.IsAdicRing A] (structureHom : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    (toDerivedComplete structureHom I hI).IsEquivalence :=
  sorry


end AlgebraicGeometry.GroupoidsOver
