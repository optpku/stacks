/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Definition_92_22_1_Cotangent
public import stacks_project.Chap92.Lemma_92_3_4_DirectLimit
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
/-!
# Objectwise homology of the ring-level cotangent complex

This module owns the `B`-module presheaf `U ↦ H^i(L(B(U)/A(U)))` attached to a homomorphism
of sheaves of commutative rings, together with its associated sheaf of `B`-modules.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open HomologicalComplex
open Opposite
open PresheafOfModules.DifferentialsConstruction
open SheafOfModules.RingedSite
open scoped Simplicial
open scoped IteratedEndofunctor

noncomputable section

universe u

namespace SheafOfModules.RingedSite.CotangentComplex.Homology

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
variable {A B : Sheaf J CommRingCat.{u}}

/-- The degree-`i` homology of the ring-level cotangent complex of `φ` on an object of the
site. -/
def obj (φ : A ⟶ B) (i : ℤ) (X : Cᵒᵖ) : ModuleCat (B.obj.obj X) :=
  (RingHom.cotangentComplex (φ.hom.app X).hom).homology i

/-- The cochain map `L(B(X)/A(X)) ⟶ restrictScalars(L(B(Y)/A(Y)))` induced by restriction
along `f : X ⟶ Y`. -/
def complexMap (φ : A ⟶ B) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    RingHom.cotangentComplex (φ.hom.app X).hom ⟶
      ((ModuleCat.restrictScalars (B.obj.map f).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (RingHom.cotangentComplex (φ.hom.app Y).hom) where
  f n :=
    (ModuleCat.extendRestrictScalarsAdj (B.obj.map f).hom).homEquiv _ _
      ((Algebra.CotangentComplex.map (φ.hom.app X).hom (φ.hom.app Y).hom
          (A.obj.map f).hom (B.obj.map f).hom
          (congrArg CommRingCat.Hom.hom (φ.hom.naturality f))).f n)
  comm' := sorry

/-- Identifying the short complex of a restricted cotangent complex with the restricted
short complex of the original cotangent complex. -/
def scRestrictIso (φ : A ⟶ B) (i : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ((((ModuleCat.restrictScalars (B.obj.map f).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (RingHom.cotangentComplex (φ.hom.app Y).hom)).sc i) ≅
      ((RingHom.cotangentComplex (φ.hom.app Y).hom).sc i).map
        (ModuleCat.restrictScalars (B.obj.map f).hom) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)

/-- Homology of the restricted ring-level cotangent complex, as restriction of scalars of
objectwise homology. -/
def restrictHomologyIso (φ : A ⟶ B) (i : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ((((ModuleCat.restrictScalars (B.obj.map f).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (RingHom.cotangentComplex (φ.hom.app Y).hom)).homology i) ≅
      (ModuleCat.restrictScalars (B.obj.map f).hom).obj (obj φ i Y) :=
  ShortComplex.homologyMapIso (scRestrictIso φ i f) ≪≫
    ((RingHom.cotangentComplex (φ.hom.app Y).hom).sc i).mapHomologyIso
      (ModuleCat.restrictScalars (B.obj.map f).hom)

/-- Restriction of objectwise cotangent homology along a morphism of the site. -/
def map (φ : A ⟶ B) (i : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    obj φ i X ⟶
      (ModuleCat.restrictScalars ((ringSheaf J B).obj.map f).hom).obj (obj φ i Y) :=
  homologyMap (complexMap φ f) i ≫ (restrictHomologyIso φ i f).hom

/-- The presheaf of `B`-modules with value `U ↦ H^i(L(B(U)/A(U)))`. -/
def presheaf (φ : A ⟶ B) (i : ℤ) : PresheafOfModules (ringSheaf J B).obj where
  obj X := obj φ i X
  map f := map φ i f
  map_id _ := sorry
  map_comp _ _ := sorry

/-- Unfolding of the objectwise value of `presheaf`. -/
theorem presheaf_obj (φ : A ⟶ B) (i : ℤ) (X : Cᵒᵖ) :
    (presheaf φ i).obj X = obj φ i X :=
  sorry

/-- The sheaf of `B`-modules associated to `U ↦ H^i(L(B(U)/A(U)))`. -/
def sheafify (φ : A ⟶ B) (i : ℤ) : SheafOfModules (ringSheaf J B) :=
  (PresheafOfModules.sheafification (𝟙 (ringSheaf J B).obj)).obj (presheaf φ i)

/-- The sheaf-level cotangent complex of a homomorphism of sheaves of rings. -/
abbrev cotangentComplex (φ : A ⟶ B) :
    CochainComplex (SheafOfModules (ringSheaf J B)) ℤ :=
  SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)

/-- Evaluation of sheaves of `B`-modules on an object of the site. -/
abbrev eval (X : Cᵒᵖ) :
    SheafOfModules.{u} (ringSheaf J B) ⥤ ModuleCat.{u} ((ringSheaf J B).obj.obj X) :=
  SheafOfModules.evaluation.{u} (ringSheaf J B) X

/-- The canonical `A(X)`-algebra map from the degree-zero ring-level standard term
to the sections of the sheaf-level polynomial presentation. -/
def standardTermUnderMapZero (φ : A ⟶ B) (X : Cᵒᵖ) :
    CommRingCat.Under.CotangentComplex.standardTerm
        (A.obj.obj X) (Under.mk (φ.hom.app X)) (op ⦋0⦌) ⟶
      Under.mk ((standardTerm A (Under.mk φ) (op ⦋0⦌)).hom.hom.app X) :=
  ((CommRingCat.Under.FreeAlgebra.adjunction (A.obj.obj X)).homEquiv
      ((CategoryTheory.forget CommRingCat.{u}).obj (B.obj.obj X))
      (Under.mk ((standardTerm A (Under.mk φ) (op ⦋0⦌)).hom.hom.app X))).symm
    ((CategoryTheory.Sheaf.FreeAlgebra.Presentation.generator A
        (Under.mk φ)).hom.app X)

/-- The free `A(X)`-algebra on sections of an `A`-algebra sheaf maps to the sections of the
free `A`-algebra sheaf. -/
def freeSectionsMap (Y : Under A) (X : Cᵒᵖ) :
    (CommRingCat.Under.FreeAlgebra.adjunction (A.obj.obj X)).toComonad.toFunctor.obj
        (Under.mk (Y.hom.hom.app X)) ⟶
      Under.mk
        (((SheafOfModules.RingedSite.CotangentComplex.freeForgetAdjunction A).toComonad.toFunctor.obj
            Y).hom.hom.app X) :=
  ((CommRingCat.Under.FreeAlgebra.adjunction (A.obj.obj X)).homEquiv
      (((Under.forget A ⋙
            sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj Y).obj.obj X)
      (Under.mk
        (((SheafOfModules.RingedSite.CotangentComplex.freeForgetAdjunction A).toComonad.toFunctor.obj
            Y).hom.hom.app X))).symm
    (((SheafOfModules.RingedSite.CotangentComplex.freeForgetAdjunction A).unit.app
        ((Under.forget A ⋙
            sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj Y)).hom.app X)

/-- The canonical `A(X)`-algebra map from a ring-level standard-resolution term to the
sections of the corresponding sheaf-level standard-resolution term. -/
def standardTermUnderMap (φ : A ⟶ B) (X : Cᵒᵖ) :
    ∀ n : ℕ,
      CommRingCat.Under.CotangentComplex.standardTerm
          (A.obj.obj X) (Under.mk (φ.hom.app X)) (op ⦋n⦌) ⟶
        Under.mk ((standardTerm A (Under.mk φ) (op ⦋n⦌)).hom.hom.app X)
  | 0 => standardTermUnderMapZero φ X
  | n + 1 =>
      (CommRingCat.Under.FreeAlgebra.adjunction
            (A.obj.obj X)).toComonad.toFunctor.map
          (standardTermUnderMap φ X n) ≫
        freeSectionsMap (standardTerm A (Under.mk φ) (op ⦋n⦌)) X

/-- Ring-level and sheaf-level standard-resolution augmentations are compatible with
`standardTermUnderMap`. -/
theorem standardTermUnderMap_comp_augmentation (φ : A ⟶ B) (X : Cᵒᵖ) (n : ℕ) :
    (CommRingCat.Under.CotangentComplex.standardAugmentation
          (A.obj.obj X) (Under.mk (φ.hom.app X)) (op ⦋n⦌)).hom =
      ((standardAugmentation A (Under.mk φ) (op ⦋n⦌)).hom.app X).hom.comp
        (standardTermUnderMap φ X n).right.hom :=
  sorry

/-- The objectwise unit from ring-level Kähler differentials of a sheaf homomorphism to
the sections of the sheaf of relative differentials. -/
def differentialsEvaluationUnit {O₁ O₂ : Sheaf J CommRingCat.{u}} (ψ : O₁ ⟶ O₂)
    (X : Cᵒᵖ) :
    CommRingCat.KaehlerDifferential (ψ.hom.app X) ⟶
      (relativeDifferentials ψ).val.obj X :=
  ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheaf J O₂).obj)).unit.app
    (relativeDifferentials' ψ.hom)).app X

/-- The Kähler-differential comparison induced by `standardTermUnderMap`. -/
def simplicialDifferentialsSections (φ : A ⟶ B) (X : Cᵒᵖ) (n : ℕ) :
    CommRingCat.KaehlerDifferential
        (CommRingCat.Under.CotangentComplex.standardTerm
          (A.obj.obj X) (Under.mk (φ.hom.app X)) (op ⦋n⦌)).hom ⟶
      (ModuleCat.restrictScalars (standardTermUnderMap φ X n).right.hom).obj
        (CommRingCat.KaehlerDifferential
          ((standardTerm A (Under.mk φ) (op ⦋n⦌)).hom.hom.app X)) :=
  CommRingCat.KaehlerDifferential.map
    ((Category.id_comp ((standardTerm A (Under.mk φ) (op ⦋n⦌)).hom.hom.app X)).trans
      (standardTermUnderMap φ X n).w.symm)

/-- Objectwise comparison from Kähler differentials of the evaluated sheaf-level
standard term to the restricted evaluation of the sheaf-level simplicial tensor term. -/
def omegaToRestrictedSimplicial (φ : A ⟶ B) (X : Cᵒᵖ) (n : ℕ) :
    CommRingCat.KaehlerDifferential
        ((standardTerm A (Under.mk φ) (op ⦋n⦌)).hom.hom.app X) ⟶
      (ModuleCat.restrictScalars
          ((standardAugmentation A (Under.mk φ) (op ⦋n⦌)).hom.app X).hom).obj
        ((eval X).obj ((simplicialModule A (Under.mk φ)).obj (op ⦋n⦌))) :=
  differentialsEvaluationUnit (standardTerm A (Under.mk φ) (op ⦋n⦌)).hom X ≫
    (((extendRestrictAdj (standardAugmentation A (Under.mk φ) (op ⦋n⦌))).unit.app
        (relativeDifferentials (standardTerm A (Under.mk φ) (op ⦋n⦌)).hom)).val.app X)

/-- The map on simplicial tensor terms from ring-level cotangent homology generators to
the evaluated sheaf-level simplicial tensor term. -/
def simplicialSectionsMap (φ : A ⟶ B) (X : Cᵒᵖ) (n : ℕ) :
    (CommRingCat.Under.CotangentComplex.simplicialModule
        (A.obj.obj X) (Under.mk (φ.hom.app X))).obj (op ⦋n⦌) ⟶
      (eval X).obj ((simplicialModule A (Under.mk φ)).obj (op ⦋n⦌)) :=
  ((ModuleCat.extendRestrictScalarsAdj
        (CommRingCat.Under.CotangentComplex.standardAugmentation
          (A.obj.obj X) (Under.mk (φ.hom.app X)) (op ⦋n⦌)).hom).homEquiv _ _).symm
    (simplicialDifferentialsSections φ X n ≫
      (ModuleCat.restrictScalars (standardTermUnderMap φ X n).right.hom).map
        (omegaToRestrictedSimplicial φ X n) ≫
      (ModuleCat.restrictScalarsComp'
          (standardTermUnderMap φ X n).right.hom
          ((standardAugmentation A (Under.mk φ) (op ⦋n⦌)).hom.app X).hom
          (CommRingCat.Under.CotangentComplex.standardAugmentation
            (A.obj.obj X) (Under.mk (φ.hom.app X)) (op ⦋n⦌)).hom
          (standardTermUnderMap_comp_augmentation φ X n)).inv.app _)

/-- Degreewise comparison of ring-level and evaluated sheaf-level cotangent complexes. -/
def sectionsComplexMap_f (φ : A ⟶ B) (X : Cᵒᵖ) (i : ℤ) :
    (RingHom.cotangentComplex (φ.hom.app X).hom).X i ⟶
      (((eval X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (cotangentComplex φ)).X i :=
  match h : ComplexShape.embeddingDownNat.r i with
  | some n =>
      (extendXIso
            ((alternatingFaceMapComplex
                (ModuleCat.{u} (B.obj.obj X))).obj
              (CommRingCat.Under.CotangentComplex.simplicialModule
                (A.obj.obj X) (Under.mk (φ.hom.app X))))
            ComplexShape.embeddingDownNat
            (ComplexShape.embeddingDownNat.f_eq_of_r_eq_some h)).hom ≫
        simplicialSectionsMap φ X n ≫
        (eval X).map
          (extendXIso
              ((alternatingFaceMapComplex
                  (SheafOfModules (ringSheaf J B))).obj
                (simplicialModule A (Under.mk φ)))
              ComplexShape.embeddingDownNat
              (ComplexShape.embeddingDownNat.f_eq_of_r_eq_some h)).inv
  | none => 0

/-- The cochain map `L(B(X)/A(X)) ⟶ L(φ)(X)` induced by comparing standard-resolution
terms after evaluating the sheaf-level cotangent complex. -/
def sectionsComplexMap (φ : A ⟶ B) (X : Cᵒᵖ) :
    RingHom.cotangentComplex (φ.hom.app X).hom ⟶
      ((eval X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (cotangentComplex φ) where
  f i := sectionsComplexMap_f φ X i
  comm' := sorry

/-- Identifying the short complex of the evaluated sheaf cotangent complex with the
evaluated short complex. -/
def scEvaluationIso (φ : A ⟶ B) (i : ℤ) (X : Cᵒᵖ) :
    ((((eval X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (cotangentComplex φ)).sc i) ≅
      ((cotangentComplex φ).sc i).map (eval X) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) sorry sorry

/-- Evaluation of sheaves of modules identifies cycles of the evaluated short complex of
`L(φ)` with the evaluated cycles. -/
def cyclesEvaluationIso (φ : A ⟶ B) (i : ℤ) (X : Cᵒᵖ) :
    (((cotangentComplex φ).sc i).map (eval X)).cycles ≅
      (eval X).obj ((cotangentComplex φ).sc i).cycles :=
  ShortComplex.cyclesIsoKernel _ ≪≫
    (PreservesKernel.iso (eval X) ((cotangentComplex φ).sc i).g).symm ≪≫
    (eval X).mapIso (ShortComplex.cyclesIsoKernel ((cotangentComplex φ).sc i)).symm

/-- Homology of the evaluated sheaf-level cotangent complex maps to the evaluation of
sheaf homology. -/
def homologyEvaluationComparison (φ : A ⟶ B) (i : ℤ) (X : Cᵒᵖ) :
    ((((eval X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (cotangentComplex φ)).homology i) ⟶
      (eval X).obj ((cotangentComplex φ).homology i) :=
  (ShortComplex.homologyMapIso (scEvaluationIso φ i X)).hom ≫
    (((cotangentComplex φ).sc i).map (eval X)).descHomology
      ((cyclesEvaluationIso φ i X).hom ≫
        (eval X).map ((cotangentComplex φ).sc i).homologyπ)
      sorry

/-- Objectwise comparison from ring-level cotangent homology to sections of the homology
sheaf of `L(φ)`. -/
def presheafComparisonApp (φ : A ⟶ B) (i : ℤ) (X : Cᵒᵖ) :
    obj φ i X ⟶
      ((SheafOfModules.forget (ringSheaf J B)).obj
        ((cotangentComplex φ).homology i)).obj X :=
  homologyMap (sectionsComplexMap φ X) i ≫ homologyEvaluationComparison φ i X

/-- The morphism of `B`-module presheaves sending `U ↦ H^i(L(B(U)/A(U)))` to the
underlying presheaf of `H^i(L(φ))`. -/
def presheafComparison (φ : A ⟶ B) (i : ℤ) :
    presheaf φ i ⟶
      (PresheafOfModules.restrictScalars (𝟙 (ringSheaf J B).obj)).obj
        ((SheafOfModules.forget (ringSheaf J B)).obj
          ((cotangentComplex φ).homology i)) where
  app X := presheafComparisonApp φ i X
  naturality := sorry

/-- The canonical comparison from the associated sheaf of `U ↦ H^i(L(B(U)/A(U)))` to
the cohomology sheaf `H^i(L(φ))`. -/
def comparison (φ : A ⟶ B) (i : ℤ) :
    sheafify φ i ⟶ (cotangentComplex φ).homology i :=
  (PresheafOfModules.sheafificationHomEquiv
      (𝟙 (ringSheaf J B).obj)).symm (presheafComparison φ i)

/-- The comparison morphism is the sheafification adjunct of `presheafComparison`. -/
theorem comparison_spec (φ : A ⟶ B) (i : ℤ) :
    PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J B).obj)
        (comparison φ i) =
      presheafComparison φ i :=
  sorry

end SheafOfModules.RingedSite.CotangentComplex.Homology

