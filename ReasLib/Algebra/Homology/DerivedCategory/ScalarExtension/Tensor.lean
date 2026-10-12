/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.Algebra.Homology.HomotopyCategory.Monoidal.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Bifunctor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Bifunctor.Monoidal
public import ReasLib.CategoryTheory.Functor.Derived.TensorComparison
public import ReasLib.CategoryTheory.Monoidal.Functor.TensorComparison
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Tensor preservation for derived scalar extension

@stack 064M

This leaf owns the derived tensor comparison attached to extension of scalars.  The homotopy-level
tensorator and the two left-derived model conditions are named separately, so downstream proofs can
reuse exactly the certificate they have.  The optional bridge to the ambient derived-category
tensor is explicit: no monoidal structure or model identification is manufactured here.

The convenience aliases in this file use the aligned module universe `ModuleCat.{u, u}`.  The
carrier-polymorphic scalar-extension and `RHom.At` APIs remain the owners for independent ring and
carrier universes.  The model-family bridge also expects its `Model` values to be built over the
ambient `MonoidalCategory` instances in scope; downstream code should preserve those instances
rather than rebinding them locally.
-/

open CategoryTheory CategoryTheory.DerivedCategory CategoryTheory.Limits
  CategoryTheory.MonoidalCategory ComplexShape
open CategoryTheory.Functor.LeftDerived

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.DerivedExtension.Tensor

variable {R S : Type u} [CommRing R] [CommRing S]
variable (σ : R →+* S)

/-- `064M:` The homotopy category of modules over a commutative ring in the aligned universe. -/
@[stacks 064M "aligned module homotopy category"]
abbrev homotopy (A : Type u) [CommRing A] :=
  HomotopyCategory (ModuleCat.{u} A) (up ℤ)

/-- `064M:` The derived category of modules over a commutative ring in the aligned universe. -/
@[stacks 064M "aligned module derived category"]
abbrev derived (A : Type u) [CommRing A] :=
  DerivedCategory (ModuleCat.{u} A)

/-- `064M:` The canonical homotopy-to-derived localization for aligned module categories. -/
@[stacks 064M "aligned module localization"]
abbrev qh (A : Type u) [CommRing A] : homotopy A ⥤ derived A :=
  DerivedCategory.Qh

/-- `064M:` Extension of scalars on aligned module homotopy categories. -/
@[stacks 064M "homotopy extension of scalars"]
abbrev homotopyExtension : homotopy R ⥤ homotopy S :=
  (ModuleCat.extendScalars σ).mapHomotopyCategory (up ℤ)

/-- `064M:` The canonical aligned derived extension-of-scalars functor. -/
@[stacks 064M "aligned derived extension of scalars"]
abbrev extension : derived R ⥤ derived S :=
  ModuleCat.derivedExtensionOfScalars.{u, u, u} σ

/-- `064M:` The tensor bifunctor on aligned module homotopy categories. -/
@[stacks 064M "homotopy tensor bifunctor for modules"]
abbrev homotopyTensor (A : Type u) [CommRing A] :
    homotopy A × homotopy A ⥤ homotopy A :=
  MonoidalCategory.tensor (homotopy A)

/-- `064M:` The canonical two-variable derived tensor bifunctor on aligned module categories. -/
@[stacks 064M "derived tensor bifunctor for modules"]
abbrev derivedTensor (A : Type u) [CommRing A] :
    derived A × derived A ⥤ derived A :=
  DerivedCategory.DerivedTensor.Bifunctor.functor

/-- `064M:` The canonical counit from the two-variable derived tensor to homotopy-level tensor. -/
@[stacks 064M "derived tensor counit for aligned modules"]
noncomputable abbrev tensorCounit (A : Type u) [CommRing A] :
    (qh A).prod (qh A) ⋙ derivedTensor A ⟶ homotopyTensor A ⋙ qh A :=
  DerivedCategory.DerivedTensor.Bifunctor.counit ≫
    (DerivedCategory.DerivedTensor.Bifunctor.sourceFunctorIso
      (C := ModuleCat.{u} A)).inv

/-- `07A4:` The Prop-valued invertibility condition for the cochain tensor comparison of scalar
extension. -/
@[stacks 07A4 "invertible cochain tensor comparison condition"]
abbrev CochainTensorInvertible (σ : R →+* S) : Prop :=
  Functor.Homotopy.Cochain.TensorComparison.IsInvertible
    (ModuleCat.extendScalars.{u, u, u} σ)

/-- `07A4:` Extension of scalars has invertible cochain tensor comparison.  The canonical instance
reduces to preservation of the coproducts defining totalized tensor complexes. -/
@[stacks 07A4 "invertible cochain tensor comparison for scalar extension"]
instance cochainTensorInvertible (σ : R →+* S) : CochainTensorInvertible σ := by
  intro K L
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
  rw [Functor.Homotopy.Cochain.tensorComparison_isIso_iff_homotopyEquivalence]
  haveI := Functor.Cochain.tensorComparison_isIso_of_preservesColimits
    (ModuleCat.extendScalars.{u, u, u} σ) K L
  exact (HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences _).1
    (inferInstance : IsIso ((HomotopyCategory.quotient (ModuleCat.{u} S) (up ℤ)).map
      (Functor.Cochain.tensorComparison
        (ModuleCat.extendScalars.{u, u, u} σ) K L)))

/-- `07A4:` The homotopy-level tensor comparison as an isomorphism from an explicit invertibility
certificate. -/
@[stacks 07A4 "homotopy tensor comparison from an explicit certificate"]
noncomputable def homotopyTensorComparisonOf
    (h : CochainTensorInvertible σ) :
      (homotopyExtension σ).prod (homotopyExtension σ) ⋙ homotopyTensor S ≅
      homotopyTensor R ⋙ homotopyExtension σ :=
  (Functor.TensorComparison.ofCoreMonoidal (homotopyExtension σ)
    (Functor.Homotopy.Cochain.coreMonoidalOf
      (ModuleCat.extendScalars.{u, u, u} σ) h)).symm

/-- `07A4:` The canonical homotopy-level tensor comparison, using the named scalar-extension
invertibility instance. -/
@[stacks 07A4 "canonical homotopy tensor comparison for scalar extension"]
noncomputable abbrev homotopyTensorComparison :
    (homotopyExtension σ).prod (homotopyExtension σ) ⋙ homotopyTensor S ≅
      homotopyTensor R ⋙ homotopyExtension σ :=
  homotopyTensorComparisonOf σ (inferInstance)

/-- `064M:` The localization counit for aligned derived extension of scalars. -/
@[stacks 064M "derived scalar-extension localization counit"]
noncomputable abbrev extensionCounit :
    (qh R) ⋙ extension σ ⟶ homotopyExtension σ ⋙ qh S :=
  ModuleCat.derivedExtensionOfScalarsCounit σ

/-- `064M:` The product of quasi-isomorphisms used by the two-variable derived tensor model. -/
@[stacks 064M "product quasi-isomorphism property for tensor"]
abbrev tensorQis (A : Type u) [CommRing A] :
    MorphismProperty (homotopy A × homotopy A) :=
  DerivedCategory.DerivedTensor.Bifunctor.qis (C := ModuleCat.{u} A)

/-- `064M:` The raw source functor for tensoring before extension of scalars. -/
@[stacks 064M "raw source tensor-extension functor"]
noncomputable abbrev sourceRaw : homotopy R × homotopy R ⥤ derived S :=
  Functor.LeftDerived.TensorComparison.sourceRaw
    (qh S) (homotopyExtension σ) (homotopyTensor R)

/-- `064M:` The raw target functor for extension of scalars in both variables before tensoring. -/
@[stacks 064M "raw target tensor-extension functor"]
noncomputable abbrev targetRaw : homotopy R × homotopy R ⥤ derived S :=
  Functor.LeftDerived.TensorComparison.targetRaw
    (qh S) (homotopyExtension σ) (homotopyTensor S)

/-- `064M:` The source-model counit for derived tensor followed by scalar extension. -/
@[stacks 064M "source derived tensor-extension counit"]
noncomputable abbrev sourceCounit :
    (qh R).prod (qh R) ⋙ (derivedTensor R ⋙ extension σ) ⟶ sourceRaw σ :=
  Functor.LeftDerived.TensorComparison.sourceCounit
    (qh R) (qh S) (homotopyExtension σ) (extension σ)
    (homotopyTensor R) (derivedTensor R) (extensionCounit σ)
    (tensorCounit R)

/-- `064M:` The target-model counit for scalar extension in both variables followed by derived
tensoring. -/
@[stacks 064M "target derived tensor-extension counit"]
noncomputable abbrev targetCounit :
    (qh R).prod (qh R) ⋙ ((extension σ).prod (extension σ) ⋙ derivedTensor S) ⟶
      targetRaw σ :=
  Functor.LeftDerived.TensorComparison.targetCounit
    (qh R) (qh S) (homotopyExtension σ) (extension σ)
    (homotopyTensor S) (derivedTensor S) (extensionCounit σ)
    (tensorCounit S)

/-- `064M:` The source model predicate for the scalar-extension tensor comparison. -/
@[stacks 064M "source left-derived tensor-extension model"]
abbrev SourceIsLeftDerived : Prop :=
  (derivedTensor R ⋙ extension σ).IsLeftDerivedFunctor
    (sourceCounit σ) (tensorQis R)

/-- `064M:` The target model predicate for the scalar-extension tensor comparison. -/
@[stacks 064M "target left-derived tensor-extension model"]
abbrev TargetIsLeftDerived : Prop :=
  ((extension σ).prod (extension σ) ⋙ derivedTensor S).IsLeftDerivedFunctor
    (targetCounit σ) (tensorQis R)

/-- `064M:` The source model is the canonical left-derived model for the tensor-extension source. -/
@[stacks 064M "source left-derived tensor-extension instance"]
instance source_isLeftDerived (σ : R →+* S) : SourceIsLeftDerived σ := sorry

/-- `064M:` The target model is the canonical left-derived model for the tensor-extension target. -/
@[stacks 064M "target left-derived tensor-extension instance"]
instance target_isLeftDerived (σ : R →+* S) : TargetIsLeftDerived σ := sorry

/-- `064M:` The derived tensor-preservation comparison from an explicit homotopy tensorator and
target-model certificate. -/
@[stacks 064M "derived tensor comparison from explicit certificates"]
noncomputable def comparisonOf
    (τ : (homotopyExtension σ).prod (homotopyExtension σ) ⋙ homotopyTensor S ≅
      homotopyTensor R ⋙ homotopyExtension σ)
    (hTarget : TargetIsLeftDerived σ) :
    derivedTensor R ⋙ extension σ ⟶
      (extension σ).prod (extension σ) ⋙ derivedTensor S :=
  Functor.LeftDerived.TensorComparison.comparisonOf
    (qh R) (qh S) (homotopyExtension σ) (extension σ)
    (homotopyTensor R) (homotopyTensor S) (derivedTensor R) (derivedTensor S)
    (tensorQis R) (extensionCounit σ) (tensorCounit R) (tensorCounit S) τ hTarget

/-- `064M:` The canonical derived tensor-preservation comparison for scalar extension. -/
@[stacks 064M "canonical derived tensor comparison for scalar extension"]
noncomputable def comparison :
    derivedTensor R ⋙ extension σ ⟶
      (extension σ).prod (extension σ) ⋙ derivedTensor S :=
  comparisonOf σ (homotopyTensorComparison σ) (target_isLeftDerived σ)

/-- `064M:` The component of the canonical derived tensor comparison at `(K,L)`. -/
@[stacks 064M "canonical derived tensor comparison component"]
noncomputable abbrev comparisonApp (K L : derived R) :
    (derivedTensor R ⋙ extension σ).obj (K, L) ⟶
      ((extension σ).prod (extension σ) ⋙ derivedTensor S).obj (K, L) :=
  (comparison σ).app (K, L)

/-- `064M:` The named component agrees with the canonical scalar-extension comparison. -/
@[simp, stacks 064M "canonical derived tensor comparison component formula"]
theorem comparison_app (K L : derived R) :
    (comparison σ).app (K, L) = comparisonApp σ K L := rfl

/-- `064M:` The reverse derived tensor comparison from an explicit homotopy tensorator and
source-model certificate. -/
@[stacks 064M "reverse derived tensor comparison from explicit certificates"]
noncomputable def comparisonInvOf
    (τ : (homotopyExtension σ).prod (homotopyExtension σ) ⋙ homotopyTensor S ≅
      homotopyTensor R ⋙ homotopyExtension σ)
    (hSource : SourceIsLeftDerived σ) :
    (extension σ).prod (extension σ) ⋙ derivedTensor S ⟶
      derivedTensor R ⋙ extension σ :=
  Functor.LeftDerived.TensorComparison.comparisonInvOf
    (qh R) (qh S) (homotopyExtension σ) (extension σ)
    (homotopyTensor R) (homotopyTensor S) (derivedTensor R) (derivedTensor S)
    (tensorQis R) (extensionCounit σ) (tensorCounit R) (tensorCounit S) τ hSource

/-- `064M:` The canonical reverse derived tensor comparison for scalar extension. -/
@[stacks 064M "canonical reverse derived tensor comparison for scalar extension"]
noncomputable def comparisonInv :
    (extension σ).prod (extension σ) ⋙ derivedTensor S ⟶
      derivedTensor R ⋙ extension σ :=
  comparisonInvOf σ (homotopyTensorComparison σ) (source_isLeftDerived σ)

/-- `064M:` The component of the reverse derived tensor comparison at `(K,L)`. -/
@[stacks 064M "reverse derived tensor comparison component"]
noncomputable abbrev comparisonInvApp (K L : derived R) :
    ((extension σ).prod (extension σ) ⋙ derivedTensor S).obj (K, L) ⟶
      (derivedTensor R ⋙ extension σ).obj (K, L) :=
  (comparisonInv σ).app (K, L)

/-- `064M:` The named reverse component agrees with the canonical reverse comparison. -/
@[simp, stacks 064M "reverse derived tensor comparison component formula"]
theorem comparisonInv_app (K L : derived R) :
    (comparisonInv σ).app (K, L) = comparisonInvApp σ K L := rfl

/-- `064M:` The reverse explicit scalar-extension comparison satisfies the source-facing counit
equation. -/
@[stacks 064M "explicit reverse scalar-extension tensor comparison counit"]
theorem comparisonInvOf_counit
    (τ : (homotopyExtension σ).prod (homotopyExtension σ) ⋙ homotopyTensor S ≅
      homotopyTensor R ⋙ homotopyExtension σ)
    (hSource : SourceIsLeftDerived σ) :
    Functor.whiskerLeft ((qh R).prod (qh R)) (comparisonInvOf σ τ hSource) ≫
      sourceCounit σ =
        targetCounit σ ≫
          (Functor.LeftDerived.TensorComparison.rawComparisonIso
            (qh S) (homotopyExtension σ) (homotopyTensor R) (homotopyTensor S) τ).hom := by
  exact Functor.LeftDerived.TensorComparison.comparisonInvOf_counit
    (qh R) (qh S) (homotopyExtension σ) (extension σ)
    (homotopyTensor R) (homotopyTensor S) (derivedTensor R) (derivedTensor S)
    (tensorQis R) (extensionCounit σ) (tensorCounit R) (tensorCounit S) τ hSource

/-- `064M:` The canonical reverse scalar-extension comparison satisfies the source-facing counit
equation. -/
@[stacks 064M "canonical reverse scalar-extension tensor comparison counit"]
theorem comparisonInv_counit :
    Functor.whiskerLeft ((qh R).prod (qh R)) (comparisonInv σ) ≫ sourceCounit σ =
      targetCounit σ ≫
        (Functor.LeftDerived.TensorComparison.rawComparisonIso
          (qh S) (homotopyExtension σ) (homotopyTensor R) (homotopyTensor S)
          (homotopyTensorComparison σ)).hom := by
  exact Functor.LeftDerived.TensorComparison.comparisonInv_counit
    (qh R) (qh S) (homotopyExtension σ) (extension σ)
    (homotopyTensor R) (homotopyTensor S) (derivedTensor R) (derivedTensor S)
    (tensorQis R) (extensionCounit σ) (tensorCounit R) (tensorCounit S)
    (homotopyTensorComparison σ)

/-- `064M:` The explicit scalar-extension tensor comparison is invertible when both supplied
iterated models satisfy their left-derived universal properties. -/
@[stacks 064M "explicit scalar-extension tensor comparison criterion"]
theorem comparisonOf_isIso
    (τ : (homotopyExtension σ).prod (homotopyExtension σ) ⋙ homotopyTensor S ≅
      homotopyTensor R ⋙ homotopyExtension σ)
    (hSource : SourceIsLeftDerived σ) (hTarget : TargetIsLeftDerived σ) :
    IsIso (comparisonOf σ τ hTarget) := by
  change IsIso
    (Functor.LeftDerived.TensorComparison.comparisonIsoOf
      (qh R) (qh S) (homotopyExtension σ) (extension σ)
      (homotopyTensor R) (homotopyTensor S) (derivedTensor R) (derivedTensor S)
      (tensorQis R) (extensionCounit σ) (tensorCounit R) (tensorCounit S) τ
      hSource hTarget).hom
  infer_instance

/-- `064M:` The canonical scalar-extension tensor comparison is invertible. -/
@[stacks 064M "canonical scalar-extension tensor comparison isomorphism instance"]
instance comparison_isIso : IsIso (comparison σ) :=
  comparisonOf_isIso σ (homotopyTensorComparison σ)
    (source_isLeftDerived σ) (target_isLeftDerived σ)

/-- `064M:` The derived scalar-extension tensor comparison as an isomorphism with explicit
forward and reverse natural transformations. -/
@[stacks 064M "derived scalar-extension tensor comparison from explicit certificates"]
noncomputable def comparisonIsoOf
    (τ : (homotopyExtension σ).prod (homotopyExtension σ) ⋙ homotopyTensor S ≅
      homotopyTensor R ⋙ homotopyExtension σ)
    (hSource : SourceIsLeftDerived σ) (hTarget : TargetIsLeftDerived σ) :
    derivedTensor R ⋙ extension σ ≅
      (extension σ).prod (extension σ) ⋙ derivedTensor S :=
  Functor.LeftDerived.TensorComparison.comparisonIsoOf
    (qh R) (qh S) (homotopyExtension σ) (extension σ)
    (homotopyTensor R) (homotopyTensor S) (derivedTensor R) (derivedTensor S)
    (tensorQis R) (extensionCounit σ) (tensorCounit R) (tensorCounit S) τ
    hSource hTarget

/-- `064M:` The canonical aligned scalar-extension tensor comparison isomorphism. -/
@[stacks 064M, stacks 068I "canonical aligned scalar-extension tensor comparison isomorphism"]
noncomputable def comparisonIso :
    derivedTensor R ⋙ extension σ ≅
      (extension σ).prod (extension σ) ⋙ derivedTensor S :=
  comparisonIsoOf σ (homotopyTensorComparison σ)
    (source_isLeftDerived σ) (target_isLeftDerived σ)

/-- `064M:` The component isomorphism of the canonical scalar-extension tensor comparison. -/
@[stacks 064M, stacks 068I "canonical derived tensor comparison component isomorphism"]
noncomputable abbrev comparisonIsoApp (K L : derived R) :
    (derivedTensor R ⋙ extension σ).obj (K, L) ≅
      ((extension σ).prod (extension σ) ⋙ derivedTensor S).obj (K, L) :=
  (comparisonIso σ).app (K, L)

/-- `064M:` The component isomorphism is the canonical comparison component. -/
@[simp, stacks 064M "canonical derived tensor comparison component isomorphism formula"]
theorem comparisonIso_app (K L : derived R) :
    (comparisonIso σ).app (K, L) = comparisonIsoApp σ K L := rfl

/-- `064M:` The forward map of the canonical scalar-extension tensor comparison isomorphism. -/
@[simp, stacks 064M "canonical scalar-extension tensor comparison isomorphism hom"]
theorem comparisonIso_hom : (comparisonIso σ).hom = comparison σ := rfl

/-- `064M:` The reverse map of the canonical scalar-extension tensor comparison isomorphism. -/
@[simp, stacks 064M "canonical scalar-extension tensor comparison isomorphism inv"]
theorem comparisonIso_inv : (comparisonIso σ).inv = comparisonInv σ := rfl

/-- `08I3:` Transport a derived scalar-extension tensor comparison to the ambient derived-category
tensor from explicit model isomorphisms. -/
@[stacks 08I3 "ambient tensor comparison from explicit derived models"]
noncomputable def ambientTensorComparisonOf
    (τ : (homotopyExtension σ).prod (homotopyExtension σ) ⋙ homotopyTensor S ≅
      homotopyTensor R ⋙ homotopyExtension σ)
    (hSource : SourceIsLeftDerived σ) (hTarget : TargetIsLeftDerived σ)
    [MonoidalCategory (derived R)] [MonoidalCategory (derived S)]
    (eR : derivedTensor R ≅ MonoidalCategory.tensor (derived R))
    (eS : derivedTensor S ≅ MonoidalCategory.tensor (derived S)) :
    Functor.TensorComparison (extension σ) :=
  Functor.TensorComparison.ofBifunctorIso
    (extension σ) (comparisonIsoOf σ τ hSource hTarget) eR eS

/-- `08I3:` The ambient tensor comparison using the canonical aligned model certificates. -/
@[stacks 08I3 "canonical ambient tensor comparison for scalar extension"]
noncomputable def ambientTensorComparison
    [MonoidalCategory (derived R)] [MonoidalCategory (derived S)]
    (eR : derivedTensor R ≅ MonoidalCategory.tensor (derived R))
    (eS : derivedTensor S ≅ MonoidalCategory.tensor (derived S)) :
    Functor.TensorComparison (extension σ) :=
  Functor.TensorComparison.ofBifunctorIso
    (extension σ) (comparisonIso σ) eR eS

/-- `08I3:` Two-variable naturality of the ambient comparison associated to a fixed-right model
family.  It is explicit because the model family itself is only pointwise in the right factor. -/
@[stacks 08I3 "fixed-right model bifunctor naturality"]
abbrev ModelIsNatural (A : Type u) [CommRing A]
    [MonoidalCategory (derived A)]
    (M : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A)) : Prop :=
  DerivedTensor.Bifunctor.Monoidal.IsNaturalOf M
    (fun E => ModuleCat.derivedTensorBifunctorRightCompatible A E)

/-- `08I3:` Build the ambient scalar-extension tensor comparison from fixed-right model families
and explicit certificates that their pointwise comparisons are natural in both variables. -/
@[stacks 08I3 "ambient tensor comparison from coherent fixed-right models"]
noncomputable def ambientTensorComparisonOfModels
    [MonoidalCategory (derived R)] [MonoidalCategory (derived S)]
    (MR : DerivedTensor.Right.Monoidal.Model
      (C := ModuleCat.{u} R))
    (MS : DerivedTensor.Right.Monoidal.Model
      (C := ModuleCat.{u} S))
    (hR : ModelIsNatural R MR)
    (hS : ModelIsNatural S MS) :
    Functor.TensorComparison (extension σ) :=
  ambientTensorComparison σ
    (DerivedTensor.Bifunctor.Monoidal.functorIsoTensorOf
      (C := ModuleCat.{u} R) MR
      (fun E => ModuleCat.derivedTensorBifunctorRightCompatible R E) hR)
    (DerivedTensor.Bifunctor.Monoidal.functorIsoTensorOf
      (C := ModuleCat.{u} S) MS
      (fun E => ModuleCat.derivedTensorBifunctorRightCompatible S E) hS)

/-- `064M:` The counit equation characterizing an explicit derived scalar-extension tensor
comparison. -/
@[stacks 064M "explicit scalar-extension tensor comparison counit equation"]
theorem comparisonOf_counit
    (τ : (homotopyExtension σ).prod (homotopyExtension σ) ⋙ homotopyTensor S ≅
      homotopyTensor R ⋙ homotopyExtension σ)
    (hTarget : TargetIsLeftDerived σ) :
    Functor.whiskerLeft ((qh R).prod (qh R)) (comparisonOf σ τ hTarget) ≫ targetCounit σ =
      sourceCounit σ ≫
        (Functor.LeftDerived.TensorComparison.rawComparisonIso
          (qh S) (homotopyExtension σ) (homotopyTensor R) (homotopyTensor S) τ).inv := by
  exact Functor.LeftDerived.TensorComparison.comparisonOf_counit
    (qh R) (qh S) (homotopyExtension σ) (extension σ)
    (homotopyTensor R) (homotopyTensor S) (derivedTensor R) (derivedTensor S)
    (tensorQis R) (extensionCounit σ) (tensorCounit R) (tensorCounit S) τ hTarget

/-- `064M:` The counit equation characterizing the canonical derived scalar-extension tensor
comparison. -/
@[stacks 064M "canonical scalar-extension tensor comparison counit equation"]
theorem comparison_counit :
    Functor.whiskerLeft ((qh R).prod (qh R)) (comparison σ) ≫ targetCounit σ =
      sourceCounit σ ≫
        (Functor.LeftDerived.TensorComparison.rawComparisonIso
          (qh S) (homotopyExtension σ) (homotopyTensor R) (homotopyTensor S)
          (homotopyTensorComparison σ)).inv := by
  exact Functor.LeftDerived.TensorComparison.comparison_counit
    (qh R) (qh S) (homotopyExtension σ) (extension σ)
    (homotopyTensor R) (homotopyTensor S) (derivedTensor R) (derivedTensor S)
    (tensorQis R) (extensionCounit σ) (tensorCounit R) (tensorCounit S)
    (homotopyTensorComparison σ)

/-- `064M:` The generic specification of an explicit scalar-extension tensor comparison. -/
@[stacks 064M "explicit scalar-extension tensor comparison specification"]
theorem comparisonOf_isComparison
    (τ : (homotopyExtension σ).prod (homotopyExtension σ) ⋙ homotopyTensor S ≅
      homotopyTensor R ⋙ homotopyExtension σ)
    (hTarget : TargetIsLeftDerived σ) :
    Functor.LeftDerived.TensorComparison.IsComparison
      (qh R) (qh S) (homotopyExtension σ) (extension σ)
      (homotopyTensor R) (homotopyTensor S) (derivedTensor R) (derivedTensor S)
      (extensionCounit σ) (tensorCounit R) (tensorCounit S) τ
      (comparisonOf σ τ hTarget) := by
  exact Functor.LeftDerived.TensorComparison.comparisonOf_isComparison
    (qh R) (qh S) (homotopyExtension σ) (extension σ)
    (homotopyTensor R) (homotopyTensor S) (derivedTensor R) (derivedTensor S)
    (tensorQis R) (extensionCounit σ) (tensorCounit R) (tensorCounit S) τ hTarget

/-- `064M:` The generic specification of the canonical scalar-extension tensor comparison. -/
@[stacks 064M "canonical scalar-extension tensor comparison specification"]
theorem comparison_isComparison :
    Functor.LeftDerived.TensorComparison.IsComparison
      (qh R) (qh S) (homotopyExtension σ) (extension σ)
      (homotopyTensor R) (homotopyTensor S) (derivedTensor R) (derivedTensor S)
      (extensionCounit σ) (tensorCounit R) (tensorCounit S)
      (homotopyTensorComparison σ) (comparison σ) := by
  exact Functor.LeftDerived.TensorComparison.comparison_isComparison
    (qh R) (qh S) (homotopyExtension σ) (extension σ)
    (homotopyTensor R) (homotopyTensor S) (derivedTensor R) (derivedTensor S)
    (tensorQis R) (extensionCounit σ) (tensorCounit R) (tensorCounit S)
    (homotopyTensorComparison σ)

end CategoryTheory.ModuleCat.DerivedExtension.Tensor
