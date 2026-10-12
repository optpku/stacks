/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Definition_92_22_1_Cotangent
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Stalk
public import stacks_project.Chap110.Lemma_110_43_1_Cotangent
public import ReasLib.Algebra.Category.CommRingCat.Under.FreeAlgebra
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalk comparison for the sheaf cotangent complex

Canonical identification of the stalk of `L(φ)` at a site point `p` with the
algebra cotangent complex of the stalk map `A_p ⟶ B_p`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open HomologicalComplex
open Opposite
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.CotangentComplex
open PresheafOfModules.DifferentialsConstruction
open scoped SheafOfModules.RingedSite.CotangentComplex
open scoped Simplicial ZeroObject IteratedEndofunctor ChangeOfRings

open CommRingCat.Under.CotangentComplex renaming
  obj → ringObj, objXIso → ringObjXIso, simplicialModule → ringSimplicialModule,
  standardTerm → ringStandardTerm, standardAugmentation → ringStandardAugmentation

noncomputable section

universe u

namespace SheafOfModules.RingedSite.CotangentComplex

variable {C : Type u} [Category.{u} C] [LocallySmall.{u} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]

namespace Stalk

variable {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (p : Point.{u} J)

/-- The stalk of the sheaf cotangent complex `L(φ)` at a site point `p`, as a
cochain complex of modules over the stalk ring `B_p`. -/
abbrev source : CochainComplex (ModuleCat.{u} (p.stalkCommRing B)) ℤ :=
  (p.moduleStalkComplex B).obj (obj A (Under.mk φ))

/-- The algebra cotangent complex of the stalk homomorphism `A_p ⟶ B_p`. -/
abbrev target : CochainComplex (ModuleCat.{u} (p.stalkCommRing B)) ℤ :=
  ringObj (p.stalkCommRing A) (Under.mk (p.stalkCommRingMap φ))

/-- The cohomological degree `-n` term of `(L(φ))_p` is the stalk of the corresponding
simplicial tensor term. -/
def sourceXIso (n : ℕ) :
    (source φ p).X (-n) ≅
      p.moduleStalk B ((simplicialModule A (Under.mk φ)).obj (op ⦋n⦌)) :=
  (p.moduleStalkFunctor B).mapIso (objXIso A (Under.mk φ) n)

/-- The cohomological degree `-n` term of `L(B_p / A_p)` is the corresponding simplicial
tensor term of the algebra cotangent complex. -/
def targetXIso (n : ℕ) :
    (target φ p).X (-n) ≅
      (ringSimplicialModule (p.stalkCommRing A)
        (Under.mk (p.stalkCommRingMap φ))).obj (op ⦋n⦌) :=
  ringObjXIso (p.stalkCommRing A) (Under.mk (p.stalkCommRingMap φ)) n

/-- Forgetting the coefficient ring commutes with forming skyscraper sheaves. -/
def skyscraperForgetIso :
    p.skyscraperSheafFunctor (A := CommRingCat.{u}) ⋙
      sheafCompose J (CategoryTheory.forget CommRingCat.{u}) ≅
    CategoryTheory.forget CommRingCat.{u} ⋙
      p.skyscraperSheafFunctor (A := Type u) :=
  NatIso.ofComponents
    (fun R ↦
      (Functor.FullyFaithful.preimageIso (fullyFaithfulSheafToPresheaf J (Type u))
        { hom :=
            { app := fun U ↦
                (preservesLimitIso (CategoryTheory.forget CommRingCat.{u})
                  (Discrete.functor fun _ : p.fiber.obj U.unop ↦ R)).hom
              naturality := fun _ _ _ ↦ sorry }
          inv :=
            { app := fun U ↦
                (preservesLimitIso (CategoryTheory.forget CommRingCat.{u})
                  (Discrete.functor fun _ : p.fiber.obj U.unop ↦ R)).inv
              naturality := fun _ _ _ ↦ sorry }
          hom_inv_id := sorry
          inv_hom_id := sorry }))
    (fun _ ↦ sorry)

/-- Stalks of free algebra sheaves are canonically free algebras on the stalks of the
generators. -/
def freeIso (X : Sheaf J CommRingCat.{u}) :
    p.sheafFiber (A := Type u) ⋙
        CommRingCat.Under.FreeAlgebra.functor (p.sheafFiber.obj X) ≅
      Sheaf.composeAndSheafify J CommRingCat.free ⋙ Under.costar X ⋙
        Under.post p.sheafFiber :=
  Adjunction.leftAdjointUniq
    ((p.skyscraperSheafAdjunction (A := Type u)).comp
      (CommRingCat.Under.FreeAlgebra.adjunction (p.sheafFiber.obj X)))
    (((freeForgetAdjunction X).comp
        (Under.postAdjunctionLeft (p.skyscraperSheafAdjunction (A := CommRingCat.{u})))).ofNatIsoRight
      (NatIso.ofComponents (fun Y ↦ (skyscraperForgetIso p).app Y.right) (fun _ ↦ sorry)))

/-- The free–forgetful comonad commutes with taking stalks of commutative ring sheaves. -/
def comonadPullbackIso (X : Sheaf J CommRingCat.{u}) :
    (freeForgetAdjunction X).toComonad.toFunctor ⋙ Under.post p.sheafFiber ≅
      Under.post p.sheafFiber ⋙
        (CommRingCat.Under.FreeAlgebra.adjunction
          (p.sheafFiber.obj X)).toComonad.toFunctor :=
  (Functor.associator
      (Under.forget X ⋙ sheafCompose J (CategoryTheory.forget CommRingCat.{u}))
      (Sheaf.composeAndSheafify J CommRingCat.free ⋙ Under.costar X)
      (Under.post p.sheafFiber)).symm ≪≫
    Functor.isoWhiskerLeft
      (Under.forget X ⋙ sheafCompose J (CategoryTheory.forget CommRingCat.{u}))
      (freeIso p X).symm ≪≫
    Functor.associator
      (Under.forget X ⋙ sheafCompose J (CategoryTheory.forget CommRingCat.{u}))
      (p.sheafFiber (A := Type u))
      (CommRingCat.Under.FreeAlgebra.functor (p.sheafFiber.obj X)) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (Under.forget X)
        (p.sheafFiberCompIso (CategoryTheory.forget CommRingCat.{u})))
      (CommRingCat.Under.FreeAlgebra.functor (p.sheafFiber.obj X)) ≪≫
    Functor.associator
      (Under.post p.sheafFiber)
      (Under.forget (p.sheafFiber.obj X) ⋙ CategoryTheory.forget CommRingCat.{u})
      (CommRingCat.Under.FreeAlgebra.functor (p.sheafFiber.obj X))

/-- Positive iterates of the free–forgetful comonad commute with taking stalks. -/
def iteratePullbackIso (X : Sheaf J CommRingCat.{u}) :
    ∀ n : ℕ,
      (freeForgetAdjunction X).toComonad.toFunctor ⁺⦋n⦌ ⋙
          Under.post p.sheafFiber ≅
        Under.post p.sheafFiber ⋙
          (CommRingCat.Under.FreeAlgebra.adjunction
            (p.sheafFiber.obj X)).toComonad.toFunctor ⁺⦋n⦌
  | 0 =>
      Functor.isoWhiskerRight
          (Endofunctor.iterate.oneIso
            (freeForgetAdjunction X).toComonad.toFunctor)
          (Under.post p.sheafFiber) ≪≫
        comonadPullbackIso p X ≪≫
        Functor.isoWhiskerLeft (Under.post p.sheafFiber)
          (Endofunctor.iterate.oneIso
            (CommRingCat.Under.FreeAlgebra.adjunction
              (p.sheafFiber.obj X)).toComonad.toFunctor).symm
  | n + 1 =>
      Functor.isoWhiskerRight
          (IteratedEndofunctor.prependIso
            (freeForgetAdjunction X).toComonad.toFunctor n).symm
          (Under.post p.sheafFiber) ≪≫
        (Functor.associator
          (freeForgetAdjunction X).toComonad.toFunctor
          ((freeForgetAdjunction X).toComonad.toFunctor ⁺⦋n⦌)
          (Under.post p.sheafFiber)).symm ≪≫
        Functor.isoWhiskerLeft (freeForgetAdjunction X).toComonad.toFunctor
          (iteratePullbackIso X n) ≪≫
        Functor.associator
          (freeForgetAdjunction X).toComonad.toFunctor
          (Under.post p.sheafFiber)
          ((CommRingCat.Under.FreeAlgebra.adjunction
            (p.sheafFiber.obj X)).toComonad.toFunctor ⁺⦋n⦌) ≪≫
        Functor.isoWhiskerRight (comonadPullbackIso p X)
          ((CommRingCat.Under.FreeAlgebra.adjunction
            (p.sheafFiber.obj X)).toComonad.toFunctor ⁺⦋n⦌) ≪≫
        (Functor.associator
          (Under.post p.sheafFiber)
          (CommRingCat.Under.FreeAlgebra.adjunction
            (p.sheafFiber.obj X)).toComonad.toFunctor
          ((CommRingCat.Under.FreeAlgebra.adjunction
            (p.sheafFiber.obj X)).toComonad.toFunctor ⁺⦋n⦌)).symm ≪≫
        Functor.isoWhiskerLeft (Under.post p.sheafFiber)
          (IteratedEndofunctor.prependIso
            (CommRingCat.Under.FreeAlgebra.adjunction
              (p.sheafFiber.obj X)).toComonad.toFunctor n)

/-- Stalk of a sheaf standard-resolution term, as an algebra under `A_p`. -/
abbrev pulledTerm (n : SimplexCategoryᵒᵖ) :
    Under (p.stalkCommRing A) :=
  (Under.post p.sheafFiber).obj (standardTerm A (Under.mk φ) n)

/-- The standard-resolution term of the stalk homomorphism `A_p ⟶ B_p`. -/
abbrev targetTerm (n : SimplexCategoryᵒᵖ) :
    Under (p.stalkCommRing A) :=
  ringStandardTerm (p.stalkCommRing A) (Under.mk (p.stalkCommRingMap φ)) n

/-- Taking stalks identifies sheaf standard-resolution terms with the polynomial-resolution
terms of the stalk homomorphism. -/
def standardTermIso (n : ℕ) :
    pulledTerm φ p (op ⦋n⦌) ≅ targetTerm φ p (op ⦋n⦌) :=
  (iteratePullbackIso p A n).app (Under.mk φ)

/-- The stalk of a sheaf-resolution augmentation agrees with the algebra-resolution
augmentation after `standardTermIso`. -/
theorem standardTermIso_comp_augmentation (n : ℕ) :
    (standardTermIso φ p n).hom.right ≫
        ringStandardAugmentation (p.stalkCommRing A)
          (Under.mk (p.stalkCommRingMap φ)) (op ⦋n⦌) =
      p.stalkCommRingMap (standardAugmentation A (Under.mk φ) (op ⦋n⦌)) :=
  sorry

/-- The inverse of `standardTermIso_comp_augmentation`. -/
theorem standardTermIso_comp_augmentation_inv (n : ℕ) :
    (standardTermIso φ p n).inv.right ≫
        p.stalkCommRingMap (standardAugmentation A (Under.mk φ) (op ⦋n⦌)) =
      ringStandardAugmentation (p.stalkCommRing A)
        (Under.mk (p.stalkCommRingMap φ)) (op ⦋n⦌) :=
  sorry

/-- Ring-hom form of compatibility of `standardTermIso` with the two augmentations. -/
theorem standardTermIso_comp_augmentation_hom (n : ℕ) :
    (p.stalkCommRingMap (standardAugmentation A (Under.mk φ) (op ⦋n⦌))).hom =
      (ringStandardAugmentation (p.stalkCommRing A)
          (Under.mk (p.stalkCommRingMap φ)) (op ⦋n⦌)).hom.comp
        (standardTermIso φ p n).hom.right.hom :=
  sorry

/-- Ring-hom form of the inverse compatibility of `standardTermIso` with the two
augmentations. -/
theorem standardTermIso_comp_augmentation_inv_hom (n : ℕ) :
    (ringStandardAugmentation (p.stalkCommRing A)
        (Under.mk (p.stalkCommRingMap φ)) (op ⦋n⦌)).hom =
      (p.stalkCommRingMap (standardAugmentation A (Under.mk φ) (op ⦋n⦌))).hom.comp
        (standardTermIso φ p n).inv.right.hom :=
  sorry

/-- Algebra-level comparison of simplicial tensor terms along `standardTermIso`. -/
def standardTermTensorIso (n : ℕ) :
    (ModuleCat.extendScalars
        (p.stalkCommRingMap (standardAugmentation A (Under.mk φ) (op ⦋n⦌))).hom).obj
      (CommRingCat.KaehlerDifferential (pulledTerm φ p (op ⦋n⦌)).hom) ≅
      (ringSimplicialModule (p.stalkCommRing A)
        (Under.mk (p.stalkCommRingMap φ))).obj (op ⦋n⦌) where
  hom :=
    ((ModuleCat.extendRestrictScalarsAdj
        (p.stalkCommRingMap (standardAugmentation A (Under.mk φ) (op ⦋n⦌))).hom).homEquiv
      _ _).symm
      (CommRingCat.KaehlerDifferential.map
          (g' := (standardTermIso φ p n).hom.right)
          ((Category.id_comp (targetTerm φ p (op ⦋n⦌)).hom).trans
            (standardTermIso φ p n).hom.w.symm) ≫
        (ModuleCat.restrictScalars (standardTermIso φ p n).hom.right.hom).map
          ((ModuleCat.extendRestrictScalarsAdj
              (ringStandardAugmentation (p.stalkCommRing A)
                (Under.mk (p.stalkCommRingMap φ)) (op ⦋n⦌)).hom).unit.app
            (CommRingCat.KaehlerDifferential (targetTerm φ p (op ⦋n⦌)).hom)) ≫
        (ModuleCat.restrictScalarsComp'
            (standardTermIso φ p n).hom.right.hom
            (ringStandardAugmentation (p.stalkCommRing A)
              (Under.mk (p.stalkCommRingMap φ)) (op ⦋n⦌)).hom
            (p.stalkCommRingMap (standardAugmentation A (Under.mk φ) (op ⦋n⦌))).hom
            (standardTermIso_comp_augmentation_hom φ p n)).inv.app _)
  inv :=
    ((ModuleCat.extendRestrictScalarsAdj
        (ringStandardAugmentation (p.stalkCommRing A)
          (Under.mk (p.stalkCommRingMap φ)) (op ⦋n⦌)).hom).homEquiv _ _).symm
      (CommRingCat.KaehlerDifferential.map
          (g' := (standardTermIso φ p n).inv.right)
          ((Category.id_comp (pulledTerm φ p (op ⦋n⦌)).hom).trans
            (standardTermIso φ p n).inv.w.symm) ≫
        (ModuleCat.restrictScalars (standardTermIso φ p n).inv.right.hom).map
          ((ModuleCat.extendRestrictScalarsAdj
              (p.stalkCommRingMap
                (standardAugmentation A (Under.mk φ) (op ⦋n⦌))).hom).unit.app
            (CommRingCat.KaehlerDifferential (pulledTerm φ p (op ⦋n⦌)).hom)) ≫
        (ModuleCat.restrictScalarsComp'
            (standardTermIso φ p n).inv.right.hom
            (p.stalkCommRingMap (standardAugmentation A (Under.mk φ) (op ⦋n⦌))).hom
            (ringStandardAugmentation (p.stalkCommRing A)
              (Under.mk (p.stalkCommRingMap φ)) (op ⦋n⦌)).hom
            (standardTermIso_comp_augmentation_inv_hom φ p n)).inv.app _)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Additive natural transformation underlying the universal relative derivation. -/
def derivationAddNatTrans {X Y : Sheaf J CommRingCat.{u}} (ψ : X ⟶ Y) :
    Y.obj ⋙ forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat.{u} ⟶
      (relativeDifferentials ψ).val.presheaf where
  app _ := AddCommGrpCat.ofHom (relativeDifferential ψ).d
  naturality _ _ _ := sorry

/-- Inverse comparison from Kahler differentials of a stalk homomorphism to the stalk of
sheaf relative differentials, induced by the stalk of the universal derivation. -/
def differentialsStalkInv {X Y : Sheaf J CommRingCat.{u}} (ψ : X ⟶ Y) :
    CommRingCat.KaehlerDifferential (p.stalkCommRingMap ψ) ⟶
      p.moduleStalk Y (relativeDifferentials ψ) :=
  (ModuleCat.Derivation.mk
      (fun b ↦ (p.presheafFiber.map (derivationAddNatTrans ψ))
        ((p.presheafFiberCompIso
            (forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat.{u})).inv.app
          Y.obj b))
      (fun _ _ ↦ sorry) (fun _ _ ↦ sorry) (fun _ ↦ sorry)).desc

/-- Objectwise map from the presheaf of relative differentials to the skyscraper of Kahler
differentials of the stalk homomorphism. -/
def differentialsPresheafToSkyscraper {X Y : Sheaf J CommRingCat.{u}} (ψ : X ⟶ Y) :
    (relativeDifferentials' ψ.hom).presheaf ⟶
      p.skyscraperPresheaf
        ((forget₂ (ModuleCat.{u} (p.stalkCommRing Y)) AddCommGrpCat.{u}).obj
          (CommRingCat.KaehlerDifferential (p.stalkCommRingMap ψ))) where
  app U :=
    Pi.lift (fun x ↦
      (forget₂ (ModuleCat.{u} (Y.obj.obj U)) AddCommGrpCat.{u}).map
        (CommRingCat.KaehlerDifferential.map
          (g' := p.toPresheafFiber U.unop x Y.obj)
          (p.toPresheafFiber_naturality ψ.hom U.unop x)))
  naturality _ _ _ := sorry

/-- Sheafification of the objectwise Kahler comparison, as a map of additive sheaves. -/
def differentialsToSkyscraper {X Y : Sheaf J CommRingCat.{u}} (ψ : X ⟶ Y) :
    (toSheaf (ringSheaf J Y)).obj (relativeDifferentials ψ) ⟶
      p.skyscraperSheaf
        ((forget₂ (ModuleCat.{u} (p.stalkCommRing Y)) AddCommGrpCat.{u}).obj
          (CommRingCat.KaehlerDifferential (p.stalkCommRingMap ψ))) :=
  ((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ _).symm
    (differentialsPresheafToSkyscraper p ψ)

/-- Forward comparison from the stalk of sheaf relative differentials to Kahler differentials
of the stalk homomorphism, induced by the universal derivation of the stalk map. -/
def differentialsStalkHom {X Y : Sheaf J CommRingCat.{u}} (ψ : X ⟶ Y) :
    p.moduleStalk Y (relativeDifferentials ψ) ⟶
      CommRingCat.KaehlerDifferential (p.stalkCommRingMap ψ) :=
  ConcreteCategory.ofHom
    { toFun :=
        ConcreteCategory.hom
          (((p.skyscraperSheafAdjunction (A := AddCommGrpCat.{u})).homEquiv _ _).symm
            (differentialsToSkyscraper p ψ))
      map_add' := fun _ _ ↦ sorry
      map_smul' := fun _ _ ↦ sorry }

/-- The stalk of sheaf relative differentials is canonically the Kahler module of the stalk
homomorphism. -/
def differentialsStalkIso {X Y : Sheaf J CommRingCat.{u}} (ψ : X ⟶ Y) :
    p.moduleStalk Y (relativeDifferentials ψ) ≅
      CommRingCat.KaehlerDifferential (p.stalkCommRingMap ψ) where
  hom := differentialsStalkHom p ψ
  inv := differentialsStalkInv p ψ
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Compatibility of commutative-ring stalk equivalences with a morphism of ring sheaves. -/
theorem stalkRingEquiv_comp {O₂ O₃ : Sheaf J CommRingCat.{u}} (α : O₂ ⟶ O₃) :
    (p.stalkRingEquiv O₃).symm.toRingHom.comp (p.stalkCommRingMap α).hom =
      (p.presheafFiber.map (ringSheafMap α).hom).hom.comp
        (p.stalkRingEquiv O₂).symm.toRingHom :=
  sorry

/-- Restriction of scalars on module sheaves commutes with the ring-valued module stalk. -/
def restrictSheafModuleStalkIso {O₂ O₃ : Sheaf J CommRingCat.{u}} (α : O₂ ⟶ O₃)
    (M : SheafOfModules (ringSheaf J O₃)) :
    (p.sheafModuleStalkFunctor (ringSheaf J O₂)).obj ((restrictionAlong α).obj M) ≅
      (ModuleCat.restrictScalars (p.presheafFiber.map (ringSheafMap α).hom).hom).obj
        ((p.sheafModuleStalkFunctor (ringSheaf J O₃)).obj M) :=
  { hom :=
      ConcreteCategory.ofHom
        { toFun := id
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ sorry }
    inv :=
      ConcreteCategory.ofHom
        { toFun := id
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ sorry }
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- Restriction of scalars commutes with taking module stalks. -/
def restrictStalkIso {O₂ O₃ : Sheaf J CommRingCat.{u}} (α : O₂ ⟶ O₃)
    (M : SheafOfModules (ringSheaf J O₃)) :
    p.moduleStalk O₂ ((restrictionAlong α).obj M) ≅
      (ModuleCat.restrictScalars (p.stalkCommRingMap α).hom).obj
        (p.moduleStalk O₃ M) :=
  (ModuleCat.restrictScalars (p.stalkRingEquiv O₂).symm.toRingHom).mapIso
      (restrictSheafModuleStalkIso p α M) ≪≫
    (ModuleCat.restrictScalarsComp'
        (p.stalkRingEquiv O₂).symm.toRingHom
        (p.presheafFiber.map (ringSheafMap α).hom).hom
        ((p.presheafFiber.map (ringSheafMap α).hom).hom.comp
          (p.stalkRingEquiv O₂).symm.toRingHom) rfl).symm.app _ ≪≫
    (ModuleCat.restrictScalarsCongr (stalkRingEquiv_comp p α).symm).app _ ≪≫
    (ModuleCat.restrictScalarsComp'
        (p.stalkCommRingMap α).hom
        (p.stalkRingEquiv O₃).symm.toRingHom
        ((p.stalkRingEquiv O₃).symm.toRingHom.comp (p.stalkCommRingMap α).hom) rfl).app _

/-- Inverse comparison of restriction of scalars with module stalks, as a natural transformation. -/
def restrictStalkInvNatTrans {O₂ O₃ : Sheaf J CommRingCat.{u}} (α : O₂ ⟶ O₃) :
    p.moduleStalkFunctor O₃ ⋙ ModuleCat.restrictScalars (p.stalkCommRingMap α).hom ⟶
      restrictionAlong α ⋙ p.moduleStalkFunctor O₂ where
  app M := (restrictStalkIso p α M).inv
  naturality _ _ _ := sorry

/-- The inverse of sheafification on module stalks, obtained by adjunction with the skyscraper
of the original presheaf stalk. -/
def sheafificationStalkInv {O : Sheaf J CommRingCat.{u}}
    (F : PresheafOfModules (ringSheaf J O).obj) :
    p.moduleStalk O
        ((PresheafOfModules.sheafification (𝟙 (ringSheaf J O).obj)).obj F) ⟶
      (ModuleCat.restrictScalars (p.stalkRingEquiv O).symm.toRingHom).obj
        ((p.presheafModuleStalkFunctor (ringSheaf J O)).obj F) :=
  ConcreteCategory.ofHom
    { toFun :=
        ConcreteCategory.hom
          (((p.skyscraperSheafAdjunction (A := AddCommGrpCat.{u})).homEquiv _ _).symm
            (((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ _).symm
              { app U :=
                  Pi.lift (fun x ↦ p.toPresheafFiber U.unop x F.presheaf)
                naturality _ _ _ := sorry }))
      map_add' := fun _ _ ↦ sorry
      map_smul' := fun _ _ ↦ sorry }

/-- The germ ring homomorphism from sections of a commutative ring sheaf to the stalk. -/
def germHom {O : Sheaf J CommRingCat.{u}} (U : C) (x : p.fiber.obj U) :
    (ringSheaf J O).obj.obj (op U) →+* p.stalkCommRing O :=
  ((forget₂ CommRingCat RingCat.{u}).map (p.toPresheafFiber U x O.obj)).hom

/-- The value of the module skyscraper at one object of the site. -/
def moduleSkyscraperObj {O : Sheaf J CommRingCat.{u}}
    (N : ModuleCat.{u} (p.stalkCommRing O)) (U : Cᵒᵖ) :
    ModuleCat ((ringSheaf J O).obj.obj U) :=
  ∏ᶜ fun x : p.fiber.obj U.unop ↦
    (ModuleCat.restrictScalars (germHom p U.unop x)).obj N

/-- Restriction maps of the module skyscraper, as the product reindexing along the fiber. -/
def moduleSkyscraperMap {O : Sheaf J CommRingCat.{u}}
    (N : ModuleCat.{u} (p.stalkCommRing O)) {U V : Cᵒᵖ} (i : U ⟶ V) :
    moduleSkyscraperObj p N U ⟶
      (ModuleCat.restrictScalars ((ringSheaf J O).obj.map i).hom).obj
        (moduleSkyscraperObj p N V) :=
  ConcreteCategory.ofHom
    { toFun := fun m ↦
        ConcreteCategory.hom
          (preservesLimitIso
              (ModuleCat.restrictScalars ((ringSheaf J O).obj.map i).hom)
              (Discrete.functor fun y : p.fiber.obj V.unop ↦
                (ModuleCat.restrictScalars (germHom p V.unop y)).obj N)).inv
          (ConcreteCategory.hom
            (HasLimit.isoOfNatIso
              (F := Discrete.functor fun y : p.fiber.obj V.unop ↦
                (ModuleCat.restrictScalars ((ringSheaf J O).obj.map i).hom).obj
                  ((ModuleCat.restrictScalars (germHom p V.unop y)).obj N))
              (G :=
                Discrete.functor (fun y : p.fiber.obj V.unop ↦
                    (ModuleCat.restrictScalars (germHom p V.unop y)).obj N) ⋙
                  ModuleCat.restrictScalars ((ringSheaf J O).obj.map i).hom)
              (Discrete.natIso fun _ ↦ Iso.refl _)).hom
            (ConcreteCategory.hom
              (Pi.map'
                (f := fun x : p.fiber.obj U.unop ↦
                  (ModuleCat.restrictScalars (germHom p U.unop x)).obj N)
                (g := fun y : p.fiber.obj V.unop ↦
                  (ModuleCat.restrictScalars ((ringSheaf J O).obj.map i).hom).obj
                    ((ModuleCat.restrictScalars (germHom p V.unop y)).obj N))
                (fun y : p.fiber.obj V.unop ↦ p.fiber.map i.unop y)
                (fun y : p.fiber.obj V.unop ↦
                  (ModuleCat.restrictScalarsComp'
                    ((ringSheaf J O).obj.map i).hom
                    (germHom p V.unop y)
                    (germHom p U.unop (p.fiber.map i.unop y))
                    sorry).hom.app N))
              m))
      map_add' := fun _ _ ↦ sorry
      map_smul' := fun _ _ ↦ sorry }

/-- Module-valued skyscraper presheaf attached to a stalk module at a site point. -/
def moduleSkyscraper {O : Sheaf J CommRingCat.{u}}
    (N : ModuleCat.{u} (p.stalkCommRing O)) :
    PresheafOfModules (ringSheaf J O).obj where
  obj := moduleSkyscraperObj p N
  map := moduleSkyscraperMap p N
  map_id := fun _ ↦ sorry
  map_comp := fun _ _ ↦ sorry

/-- Forgetful comparison from the module skyscraper to the additive skyscraper. -/
def moduleSkyscraperToAdd {O : Sheaf J CommRingCat.{u}}
    (N : ModuleCat.{u} (p.stalkCommRing O)) :
    (PresheafOfModules.toPresheaf (ringSheaf J O).obj).obj (moduleSkyscraper p N) ⟶
      p.skyscraperPresheaf
        ((forget₂ (ModuleCat.{u} (p.stalkCommRing O)) AddCommGrpCat.{u}).obj N) where
  app U :=
    Pi.lift fun x : p.fiber.obj U.unop ↦
      (forget₂ (ModuleCat ((ringSheaf J O).obj.obj U)) AddCommGrpCat.{u}).map
          (Pi.π (fun y : p.fiber.obj U.unop ↦
            (ModuleCat.restrictScalars (germHom p U.unop y)).obj N) x) ≫
        AddCommGrpCat.ofHom
          { toFun := id
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
  naturality := fun {_ _} _ ↦ sorry

/-- Germ of a module-presheaf section at one fiber point, as a linear map into the module
stalk. -/
def germToModuleStalk {O : Sheaf J CommRingCat.{u}}
    (M : SheafOfModules (ringSheaf J O)) (U : Cᵒᵖ) (x : p.fiber.obj U.unop) :
    M.val.obj U ⟶
      (ModuleCat.restrictScalars (germHom p U.unop x)).obj (p.moduleStalk O M) :=
  ConcreteCategory.ofHom
    { toFun := ConcreteCategory.hom (p.toPresheafFiber U.unop x M.val.presheaf)
      map_add' := fun _ _ ↦ sorry
      map_smul' := fun _ _ ↦ sorry }

/-- A module sheaf maps to the skyscraper of the scalar extension of its stalk, after
restriction of scalars along a ring-sheaf homomorphism. -/
def toRestrictedExtendSkyscraper {O₂ O₃ : Sheaf J CommRingCat.{u}} (α : O₂ ⟶ O₃)
    (M : SheafOfModules (ringSheaf J O₂)) :
    M.val ⟶
      (PresheafOfModules.pushforward (ringedSiteStructureMap α).hom).obj
        (moduleSkyscraper p
          ((ModuleCat.extendScalars (p.stalkCommRingMap α).hom).obj
            (p.moduleStalk O₂ M))) :=
  PresheafOfModules.homMk
    { app U :=
        let N :=
          (ModuleCat.extendScalars (p.stalkCommRingMap α).hom).obj
            (p.moduleStalk O₂ M)
        let G :=
          Discrete.functor fun x : p.fiber.obj U.unop ↦
            (ModuleCat.restrictScalars (germHom p (O := O₃) U.unop x)).obj N
        limit.lift (G ⋙ forget₂ (ModuleCat.{u} ((ringSheaf J O₃).obj.obj U))
            AddCommGrpCat.{u})
          { pt := M.val.presheaf.obj U
            π := Discrete.natTrans fun x ↦
              p.toPresheafFiber U.unop x.as M.val.presheaf ≫
                AddCommGrpCat.ofHom
                  { toFun := id
                    map_zero' := rfl
                    map_add' := fun _ _ ↦ rfl } ≫
                (forget₂ (ModuleCat.{u} (p.stalkCommRing O₂)) AddCommGrpCat.{u}).map
                  ((ModuleCat.extendRestrictScalarsAdj
                      (p.stalkCommRingMap α).hom).unit.app
                    (p.moduleStalk O₂ M)) ≫
                AddCommGrpCat.ofHom
                  (X :=
                    (forget₂ (ModuleCat.{u} (p.stalkCommRing O₃))
                      AddCommGrpCat.{u}).obj N)
                  (Y :=
                    (forget₂ (ModuleCat.{u} ((ringSheaf J O₃).obj.obj U))
                      AddCommGrpCat.{u}).obj (G.obj x))
                  { toFun := id
                    map_zero' := rfl
                    map_add' := fun _ _ ↦ rfl } } ≫
          (preservesLimitIso
              (forget₂ (ModuleCat.{u} ((ringSheaf J O₃).obj.obj U))
                AddCommGrpCat.{u})
              G).inv
      naturality := fun {_ _} _ ↦ sorry }
    (fun _ _ _ ↦ sorry)

/-- The canonical comparison from the presheaf-module stalk of a pullback to scalar extension
of the original module stalk. -/
def pullbackStalkToExtend {O₂ O₃ : Sheaf J CommRingCat.{u}} (α : O₂ ⟶ O₃)
    (M : SheafOfModules (ringSheaf J O₂)) :
    (ModuleCat.restrictScalars (p.stalkRingEquiv O₃).symm.toRingHom).obj
      ((p.presheafModuleStalkFunctor (ringSheaf J O₃)).obj
        ((PresheafOfModules.pullback (ringedSiteStructureMap α).hom).obj M.val)) ⟶
      (ModuleCat.extendScalars (p.stalkCommRingMap α).hom).obj (p.moduleStalk O₂ M) :=
  ConcreteCategory.ofHom
    { toFun :=
        ConcreteCategory.hom
          (p.skyscraperPresheafHomEquiv.symm
            ((PresheafOfModules.toPresheaf (ringSheaf J O₃).obj).map
                ((PresheafOfModules.pullbackPushforwardAdjunction
                    (ringedSiteStructureMap α).hom).homEquiv _ _ |>.symm
                  (toRestrictedExtendSkyscraper p α M)) ≫
              moduleSkyscraperToAdd p
                ((ModuleCat.extendScalars (p.stalkCommRingMap α).hom).obj
                  (p.moduleStalk O₂ M))))
      map_add' := fun _ _ ↦ sorry
      map_smul' := fun _ _ ↦ sorry }

/-- Stalk of a sheaf tensor term versus scalar extension of the stalk of relative
differentials. -/
def extendAlongStalkIso (n : ℕ) :
    p.moduleStalk B ((simplicialModule A (Under.mk φ)).obj (op ⦋n⦌)) ≅
      (ModuleCat.extendScalars
          (p.stalkCommRingMap (standardAugmentation A (Under.mk φ) (op ⦋n⦌))).hom).obj
        (p.moduleStalk (standardTerm A (Under.mk φ) (op ⦋n⦌)).right
          (relativeDifferentials (standardTerm A (Under.mk φ) (op ⦋n⦌)).hom)) :=
  let α := standardAugmentation A (Under.mk φ) (op ⦋n⦌)
  let Ωn := relativeDifferentials (standardTerm A (Under.mk φ) (op ⦋n⦌)).hom
  let invMap :=
    ((ModuleCat.extendRestrictScalarsAdj (p.stalkCommRingMap α).hom).homEquiv
      (p.moduleStalk (standardTerm A (Under.mk φ) (op ⦋n⦌)).right Ωn)
      (p.moduleStalk B ((simplicialModule A (Under.mk φ)).obj (op ⦋n⦌)))).symm
      ((p.moduleStalkFunctor (standardTerm A (Under.mk φ) (op ⦋n⦌)).right).map
          ((extendRestrictAdj α).unit.app Ωn) ≫
        (restrictStalkIso p α ((simplicialModule A (Under.mk φ)).obj (op ⦋n⦌))).hom)
  { hom :=
      (p.moduleStalkFunctor B).map
          ((pullbackExtendIso α).inv.app Ωn ≫
            (SheafOfModules.pullbackIso (ringedSiteStructureMap α)).hom.app Ωn) ≫
        sheafificationStalkInv p
          ((PresheafOfModules.pullback (ringedSiteStructureMap α).hom).obj Ωn.val) ≫
        pullbackStalkToExtend p α Ωn
    inv := invMap
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- Degreewise comparison of the stalk of a sheaf simplicial tensor term with the algebra
simplicial tensor term of the stalk homomorphism. -/
def termIso (n : ℕ) :
    p.moduleStalk B ((simplicialModule A (Under.mk φ)).obj (op ⦋n⦌)) ≅
      (ringSimplicialModule (p.stalkCommRing A)
        (Under.mk (p.stalkCommRingMap φ))).obj (op ⦋n⦌) :=
  (extendAlongStalkIso φ p n).trans
    (((ModuleCat.extendScalars
          (p.stalkCommRingMap (standardAugmentation A (Under.mk φ) (op ⦋n⦌))).hom).mapIso
        (differentialsStalkIso p (standardTerm A (Under.mk φ) (op ⦋n⦌)).hom)).trans
      (standardTermTensorIso φ p n))

/-- Degreewise comparison of the stalk of `L(φ)` with `L(B_p / A_p)`. -/
def appIso : ∀ n : ℤ, (source φ p).X n ≅ (target φ p).X n
  | Int.ofNat (Nat.succ k) =>
      { hom := (0 : (source φ p).X (Int.ofNat k.succ) ⟶ (target φ p).X (Int.ofNat k.succ))
        inv := (0 : (target φ p).X (Int.ofNat k.succ) ⟶ (source φ p).X (Int.ofNat k.succ))
        hom_inv_id := sorry
        inv_hom_id := sorry }
  | (0 : ℤ) =>
      (sourceXIso φ p 0).trans ((termIso φ p 0).trans (targetXIso φ p 0).symm)
  | Int.negSucc k =>
      (sourceXIso φ p k.succ).trans
        ((termIso φ p k.succ).trans (targetXIso φ p k.succ).symm)

/-- The canonical identification `(L(φ))_p ≅ L(B_p / A_p)` of cochain complexes of
`B_p`-modules. -/
def iso : source φ p ≅ target φ p :=
  Hom.isoOfComponents (appIso φ p) (fun _ _ _ ↦ sorry)

/-- The forward comparison morphism of stalk cotangent complexes. -/
def map : source φ p ⟶ target φ p :=
  (iso φ p).hom

/-- The inverse comparison morphism of stalk cotangent complexes. -/
def mapInv : target φ p ⟶ source φ p :=
  (iso φ p).inv

/-- The canonical comparison morphism is an isomorphism. -/
instance map_isIso : IsIso (map φ p) :=
  (iso φ p).isIso_hom

/-- In cohomological degree `-n`, the comparison is the stalk comparison of simplicial
tensor terms. -/
theorem iso_hom_f (n : ℕ) :
    (iso φ p).hom.f (-n) =
      (sourceXIso φ p n).hom ≫ (termIso φ p n).hom ≫ (targetXIso φ p n).inv :=
  sorry

end Stalk

end SheafOfModules.RingedSite.CotangentComplex

end
end
