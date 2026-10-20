module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex
public import ReasLib.RingTheory.CotangentComplex.Functoriality
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
private def scRestrictIso (φ : A ⟶ B) (i : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ((((ModuleCat.restrictScalars (B.obj.map f).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (RingHom.cotangentComplex (φ.hom.app Y).hom)).sc i) ≅
      ((RingHom.cotangentComplex (φ.hom.app Y).hom).sc i).map
        (ModuleCat.restrictScalars (B.obj.map f).hom) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)

/-- Homology of the restricted ring-level cotangent complex, as restriction of scalars of
objectwise homology. -/
@[no_expose] def restrictHomologyIso (φ : A ⟶ B) (i : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
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

/-- Restriction on objectwise cotangent homology respects identity morphisms. -/
theorem map_id (φ : A ⟶ B) (i : ℤ) (X : Cᵒᵖ) :
    map φ i (𝟙 X) =
      (ModuleCat.restrictScalarsId' ((ringSheaf J B).obj.map (𝟙 X)).hom
        (congrArg RingCat.Hom.hom ((ringSheaf J B).obj.map_id X))).inv.app
          (obj φ i X) :=
  sorry

/-- Restriction on objectwise cotangent homology respects composition. -/
theorem map_comp (φ : A ⟶ B) (i : ℤ) {X Y Z : Cᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    map φ i (f ≫ g) =
      map φ i f ≫ (ModuleCat.restrictScalars ((ringSheaf J B).obj.map f).hom).map
        (map φ i g) ≫
      (ModuleCat.restrictScalarsComp' ((ringSheaf J B).obj.map f).hom
        ((ringSheaf J B).obj.map g).hom ((ringSheaf J B).obj.map (f ≫ g)).hom
        (congrArg RingCat.Hom.hom ((ringSheaf J B).obj.map_comp f g))).inv.app
          (obj φ i Z) :=
  sorry

/-- The presheaf of `B`-modules with value `U ↦ H^i(L(B(U)/A(U)))`. -/
def presheaf (φ : A ⟶ B) (i : ℤ) : PresheafOfModules (ringSheaf J B).obj where
  obj X := obj φ i X
  map f := map φ i f
  map_id X := map_id φ i X
  map_comp f g := map_comp φ i f g

/-- The value of the homology presheaf is the homology of the section-ring cotangent complex. -/
theorem presheaf_obj (φ : A ⟶ B) (i : ℤ) (X : Cᵒᵖ) :
    (presheaf φ i).obj X = obj φ i X :=
  rfl

/-- The sheaf of `B`-modules associated to `U ↦ H^i(L(B(U)/A(U)))`. -/
def sheafify (φ : A ⟶ B) (i : ℤ) : SheafOfModules (ringSheaf J B) :=
  (PresheafOfModules.sheafification (𝟙 (ringSheaf J B).obj)).obj (presheaf φ i)

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
        ((SheafOfModules.evaluation.{u} (ringSheaf J B) X).obj ((simplicialModule A (Under.mk φ)).obj (op ⦋n⦌))) :=
  differentialsEvaluationUnit (standardTerm A (Under.mk φ) (op ⦋n⦌)).hom X ≫
    (((ChangeOfRings.extendRestrictAdjunction
        (ringSheafMap (standardAugmentation A (Under.mk φ) (op ⦋n⦌)))).unit.app
        (relativeDifferentials (standardTerm A (Under.mk φ) (op ⦋n⦌)).hom)).val.app X)

/-- The map on simplicial tensor terms from ring-level cotangent homology generators to
the evaluated sheaf-level simplicial tensor term. -/
def simplicialSectionsMap (φ : A ⟶ B) (X : Cᵒᵖ) (n : ℕ) :
    (CommRingCat.Under.CotangentComplex.simplicialModule
        (A.obj.obj X) (Under.mk (φ.hom.app X))).obj (op ⦋n⦌) ⟶
      (SheafOfModules.evaluation.{u} (ringSheaf J B) X).obj ((simplicialModule A (Under.mk φ)).obj (op ⦋n⦌)) :=
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
      (((SheafOfModules.evaluation.{u} (ringSheaf J B) X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ))).X i :=
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
        (SheafOfModules.evaluation.{u} (ringSheaf J B) X).map
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
      ((SheafOfModules.evaluation.{u} (ringSheaf J B) X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)) where
  f i := sectionsComplexMap_f φ X i
  comm' := sorry

/-- Identifying the short complex of the evaluated sheaf cotangent complex with the
evaluated short complex. -/
private def scEvaluationIso (φ : A ⟶ B) (i : ℤ) (X : Cᵒᵖ) :
    ((((SheafOfModules.evaluation.{u} (ringSheaf J B) X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ))).sc i) ≅
      (@ShortComplex.map _ _ _ _ _ _
        ((SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)).sc i) (SheafOfModules.evaluation.{u} (ringSheaf J B) X)
        (by constructor; intro M N; rfl)) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp only [Iso.refl_hom]; exact (Category.id_comp _).trans (Category.comp_id _).symm)
    (by simp only [Iso.refl_hom]; exact (Category.id_comp _).trans (Category.comp_id _).symm)

/-- Evaluation of sheaves of modules identifies cycles of the evaluated short complex of
`L(φ)` with the evaluated cycles. -/
private def cyclesEvaluationIso (φ : A ⟶ B) (i : ℤ) (X : Cᵒᵖ) :
    ((@ShortComplex.map _ _ _ _ _ _
        ((SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)).sc i) (SheafOfModules.evaluation.{u} (ringSheaf J B) X)
        (by constructor; intro M N; rfl))).cycles ≅
      (SheafOfModules.evaluation.{u} (ringSheaf J B) X).obj ((SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)).sc i).cycles :=
  ShortComplex.cyclesIsoKernel _ ≪≫
    (PreservesKernel.iso (SheafOfModules.evaluation.{u} (ringSheaf J B) X) ((SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)).sc i).g).symm ≪≫
    (SheafOfModules.evaluation.{u} (ringSheaf J B) X).mapIso (ShortComplex.cyclesIsoKernel ((SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)).sc i)).symm

/-- The evaluated homology projection annihilates the boundaries in the evaluated complex. -/
private theorem homologyEvaluationComparison_condition (φ : A ⟶ B) (i : ℤ) (X : Cᵒᵖ) :
    ((@ShortComplex.map _ _ _ _ _ _
        ((SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)).sc i) (SheafOfModules.evaluation.{u} (ringSheaf J B) X)
        (by constructor; intro M N; rfl))).toCycles ≫
      ((cyclesEvaluationIso φ i X).hom ≫
        (SheafOfModules.evaluation.{u} (ringSheaf J B) X).map
          ((SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)).sc i).homologyπ) = 0 :=
  sorry

/-- Homology of the evaluated sheaf-level cotangent complex maps to the evaluation of
sheaf homology. -/
@[no_expose] def homologyEvaluationComparison (φ : A ⟶ B) (i : ℤ) (X : Cᵒᵖ) :
    ((((SheafOfModules.evaluation.{u} (ringSheaf J B) X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ))).homology i) ⟶
      (SheafOfModules.evaluation.{u} (ringSheaf J B) X).obj ((SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)).homology i) :=
  (ShortComplex.homologyMapIso (scEvaluationIso φ i X)).hom ≫
    ((@ShortComplex.map _ _ _ _ _ _
        ((SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)).sc i) (SheafOfModules.evaluation.{u} (ringSheaf J B) X)
        (by constructor; intro M N; rfl))).descHomology
      ((cyclesEvaluationIso φ i X).hom ≫
        (SheafOfModules.evaluation.{u} (ringSheaf J B) X).map ((SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)).sc i).homologyπ)
      (homologyEvaluationComparison_condition φ i X)

/-- Objectwise comparison from ring-level cotangent homology to sections of the homology
sheaf of `L(φ)`. -/
def presheafComparisonApp (φ : A ⟶ B) (i : ℤ) (X : Cᵒᵖ) :
    obj φ i X ⟶
      ((SheafOfModules.forget (ringSheaf J B)).obj
        ((SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)).homology i)).obj X :=
  homologyMap (sectionsComplexMap φ X) i ≫ homologyEvaluationComparison φ i X

/-- The morphism of `B`-module presheaves sending `U ↦ H^i(L(B(U)/A(U)))` to the
underlying presheaf of `H^i(L(φ))`. -/
def presheafComparison (φ : A ⟶ B) (i : ℤ) :
    presheaf φ i ⟶
      (PresheafOfModules.restrictScalars (𝟙 (ringSheaf J B).obj)).obj
        ((SheafOfModules.forget (ringSheaf J B)).obj
          ((SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)).homology i)) where
  app X := presheafComparisonApp φ i X
  naturality := sorry

/-- The canonical comparison from the associated sheaf of `U ↦ H^i(L(B(U)/A(U)))` to
the cohomology sheaf `H^i(L(φ))`. -/
def comparison (φ : A ⟶ B) (i : ℤ) :
    sheafify φ i ⟶ (SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)).homology i :=
  (PresheafOfModules.sheafificationHomEquiv
      (𝟙 (ringSheaf J B).obj)).symm (presheafComparison φ i)

/-- The comparison morphism is the sheafification adjunct of `presheafComparison`. -/
theorem comparison_spec (φ : A ⟶ B) (i : ℤ) :
    PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J B).obj)
        (comparison φ i) =
      presheafComparison φ i :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J B).obj)).apply_symm_apply
    (presheafComparison φ i)

/-- The canonical comparison from sheafified section-ring cotangent homology to
homology of the sheaf cotangent complex is an isomorphism in every integer degree. -/
instance comparison_isIso (φ : A ⟶ B) (i : ℤ) :
    IsIso (comparison φ i) := sorry

end SheafOfModules.RingedSite.CotangentComplex.Homology

