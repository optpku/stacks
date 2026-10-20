/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Stalk
public import ReasLib.RingTheory.CotangentComplex.Basic
public import ReasLib.Algebra.Category.CommRingCat.Under.FreeAlgebra
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Sites.Sheafification

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

private def skyscraperForgetHomApp (R : CommRingCat.{u}) (U : Cᵒᵖ) :=
  (preservesLimitIso (CategoryTheory.forget CommRingCat.{u})
    (Discrete.functor fun _ : p.fiber.obj U.unop ↦ R)).hom

private def skyscraperForgetInvApp (R : CommRingCat.{u}) (U : Cᵒᵖ) :=
  (preservesLimitIso (CategoryTheory.forget CommRingCat.{u})
    (Discrete.functor fun _ : p.fiber.obj U.unop ↦ R)).inv

private theorem skyscraperForgetIso_hom_naturality (R : CommRingCat.{u})
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    ((p.skyscraperPresheaf R) ⋙ CategoryTheory.forget CommRingCat.{u}).map i ≫
        skyscraperForgetHomApp p R V =
      skyscraperForgetHomApp p R U ≫
        (p.skyscraperPresheaf ((CategoryTheory.forget CommRingCat.{u}).obj R)).map i :=
  sorry

private theorem skyscraperForgetIso_inv_naturality (R : CommRingCat.{u})
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    (p.skyscraperPresheaf ((CategoryTheory.forget CommRingCat.{u}).obj R)).map i ≫
        skyscraperForgetInvApp p R V =
      skyscraperForgetInvApp p R U ≫
        ((p.skyscraperPresheaf R) ⋙ CategoryTheory.forget CommRingCat.{u}).map i :=
  sorry

private def skyscraperForgetHom (R : CommRingCat.{u}) :
    (p.skyscraperPresheaf R) ⋙ CategoryTheory.forget CommRingCat.{u} ⟶
      p.skyscraperPresheaf ((CategoryTheory.forget CommRingCat.{u}).obj R) where
  app := skyscraperForgetHomApp p R
  naturality _ _ i := skyscraperForgetIso_hom_naturality p R i

private def skyscraperForgetInv (R : CommRingCat.{u}) :
    p.skyscraperPresheaf ((CategoryTheory.forget CommRingCat.{u}).obj R) ⟶
      (p.skyscraperPresheaf R) ⋙ CategoryTheory.forget CommRingCat.{u} where
  app := skyscraperForgetInvApp p R
  naturality _ _ i := skyscraperForgetIso_inv_naturality p R i

private theorem skyscraperForgetIso_component_laws (R : CommRingCat.{u}) :
    skyscraperForgetHom p R ≫ skyscraperForgetInv p R = 𝟙 _ ∧
      skyscraperForgetInv p R ≫ skyscraperForgetHom p R = 𝟙 _ :=
  sorry

private def skyscraperForgetComponent (R : CommRingCat.{u}) :
    (p.skyscraperSheafFunctor (A := CommRingCat.{u}) ⋙
      sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R ≅
    (CategoryTheory.forget CommRingCat.{u} ⋙
      p.skyscraperSheafFunctor (A := Type u)).obj R :=
  Functor.FullyFaithful.preimageIso (fullyFaithfulSheafToPresheaf J (Type u))
    { hom := skyscraperForgetHom p R
      inv := skyscraperForgetInv p R
      hom_inv_id := (skyscraperForgetIso_component_laws p R).1
      inv_hom_id := (skyscraperForgetIso_component_laws p R).2 }

private theorem skyscraperForgetIso_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (p.skyscraperSheafFunctor (A := CommRingCat.{u}) ⋙
      sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map f ≫
        (skyscraperForgetComponent p S).hom =
      (skyscraperForgetComponent p R).hom ≫
        (CategoryTheory.forget CommRingCat.{u} ⋙
          p.skyscraperSheafFunctor (A := Type u)).map f :=
  sorry

/-- Forgetting the coefficient ring commutes with forming skyscraper sheaves. -/
private def skyscraperForgetIso :
    p.skyscraperSheafFunctor (A := CommRingCat.{u}) ⋙
      sheafCompose J (CategoryTheory.forget CommRingCat.{u}) ≅
    CategoryTheory.forget CommRingCat.{u} ⋙
      p.skyscraperSheafFunctor (A := Type u) :=
  NatIso.ofComponents (skyscraperForgetComponent p)
    (fun f ↦ skyscraperForgetIso_naturality p f)

private theorem freeIso_naturality (X : Sheaf J CommRingCat.{u})
    {Y Z : Under (p.sheafFiber.obj X)} (f : Y ⟶ Z) :
    (p.skyscraperSheafFunctor (A := CommRingCat.{u}) ⋙
      sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map f.right ≫
          ((skyscraperForgetIso p).app Z.right).hom =
      ((skyscraperForgetIso p).app Y.right).hom ≫
        (CategoryTheory.forget CommRingCat.{u} ⋙
          p.skyscraperSheafFunctor (A := Type u)).map f.right :=
  sorry

-- Specify the canonical sheaf coproducts directly in the free-algebra functors.
/-- Stalks of free algebra sheaves are canonically free algebras on the stalks of the
generators. -/
private def freeIso (X : Sheaf J CommRingCat.{u}) :
    p.sheafFiber (A := Type u) ⋙
        CommRingCat.Under.FreeAlgebra.functor (p.sheafFiber.obj X) ≅
      Sheaf.composeAndSheafify J CommRingCat.free ⋙ (@Under.costar _ _ X
        (Sheaf.instHasColimitsOfShape (J := J) (D := CommRingCat.{u}))) ⋙
        Under.post p.sheafFiber :=
  Adjunction.leftAdjointUniq
    ((p.skyscraperSheafAdjunction (A := Type u)).comp
      (CommRingCat.Under.FreeAlgebra.adjunction (p.sheafFiber.obj X)))
    (((freeForgetAdjunction X).comp
        (Under.postAdjunctionLeft (p.skyscraperSheafAdjunction (A := CommRingCat.{u})))).ofNatIsoRight
      (NatIso.ofComponents
        (F := Under.post p.skyscraperSheafFunctor ⋙
          Under.map ((p.skyscraperSheafAdjunction (A := CommRingCat.{u})).unit.app X) ⋙
          Under.forget X ⋙ sheafCompose J (CategoryTheory.forget CommRingCat.{u}))
        (G := CommRingCat.Under.FreeAlgebra.carrier (p.sheafFiber.obj X) ⋙
          p.skyscraperSheafFunctor (A := Type u))
        (fun Y ↦ (skyscraperForgetIso p).app Y.right) (fun f ↦ freeIso_naturality p X f)))

/-- The free–forgetful comonad commutes with taking stalks of commutative ring sheaves. -/
private def comonadPullbackIso (X : Sheaf J CommRingCat.{u}) :
    (freeForgetAdjunction X).toComonad.toFunctor ⋙ Under.post p.sheafFiber ≅
      Under.post p.sheafFiber ⋙
        (CommRingCat.Under.FreeAlgebra.adjunction
          (p.sheafFiber.obj X)).toComonad.toFunctor :=
  (Functor.associator
      (Under.forget X ⋙ sheafCompose J (CategoryTheory.forget CommRingCat.{u}))
      (Sheaf.composeAndSheafify J CommRingCat.free ⋙ (@Under.costar _ _ X
        (Sheaf.instHasColimitsOfShape (J := J) (D := CommRingCat.{u}))))
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
private def iteratePullbackIso (X : Sheaf J CommRingCat.{u}) :
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
private abbrev pulledTerm (n : SimplexCategoryᵒᵖ) :
    Under (p.stalkCommRing A) :=
  (Under.post p.sheafFiber).obj (standardTerm A (Under.mk φ) n)

/-- The standard-resolution term of the stalk homomorphism `A_p ⟶ B_p`. -/
private abbrev targetTerm (n : SimplexCategoryᵒᵖ) :
    Under (p.stalkCommRing A) :=
  ringStandardTerm (p.stalkCommRing A) (Under.mk (p.stalkCommRingMap φ)) n

/-- Taking stalks identifies sheaf standard-resolution terms with the polynomial-resolution
terms of the stalk homomorphism. -/
private def standardTermIso (n : ℕ) :
    pulledTerm φ p (op ⦋n⦌) ≅ targetTerm φ p (op ⦋n⦌) :=
  (iteratePullbackIso p A n).app (Under.mk φ)

/-- The stalk of a sheaf-resolution augmentation agrees with the algebra-resolution
augmentation after `standardTermIso`. -/
private theorem standardTermIso_comp_augmentation (n : ℕ) :
    (standardTermIso φ p n).hom.right ≫
        ringStandardAugmentation (p.stalkCommRing A)
          (Under.mk (p.stalkCommRingMap φ)) (op ⦋n⦌) =
      p.stalkCommRingMap (standardAugmentation A (Under.mk φ) (op ⦋n⦌)) :=
  sorry

/-- The inverse standard-resolution stalk comparison commutes with the augmentations. -/
private theorem standardTermIso_comp_augmentation_inv (n : ℕ) :
    (standardTermIso φ p n).inv.right ≫
        p.stalkCommRingMap (standardAugmentation A (Under.mk φ) (op ⦋n⦌)) =
      ringStandardAugmentation (p.stalkCommRing A)
        (Under.mk (p.stalkCommRingMap φ)) (op ⦋n⦌) :=
  sorry

/-- Ring-hom form of compatibility of `standardTermIso` with the two augmentations. -/
private theorem standardTermIso_comp_augmentation_hom (n : ℕ) :
    (p.stalkCommRingMap (standardAugmentation A (Under.mk φ) (op ⦋n⦌))).hom =
      (ringStandardAugmentation (p.stalkCommRing A)
          (Under.mk (p.stalkCommRingMap φ)) (op ⦋n⦌)).hom.comp
        (standardTermIso φ p n).hom.right.hom :=
  sorry

/-- Ring-hom form of the inverse compatibility of `standardTermIso` with the two
augmentations. -/
private theorem standardTermIso_comp_augmentation_inv_hom (n : ℕ) :
    (ringStandardAugmentation (p.stalkCommRing A)
        (Under.mk (p.stalkCommRingMap φ)) (op ⦋n⦌)).hom =
      (p.stalkCommRingMap (standardAugmentation A (Under.mk φ) (op ⦋n⦌))).hom.comp
        (standardTermIso φ p n).inv.right.hom :=
  sorry

private def standardTermTensorIsoHom (n : ℕ) :
    (ModuleCat.extendScalars
        (p.stalkCommRingMap (standardAugmentation A (Under.mk φ) (op ⦋n⦌))).hom).obj
      (CommRingCat.KaehlerDifferential (pulledTerm φ p (op ⦋n⦌)).hom) ⟶
      (ringSimplicialModule (p.stalkCommRing A)
        (Under.mk (p.stalkCommRingMap φ))).obj (op ⦋n⦌) :=
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

private def standardTermTensorIsoInv (n : ℕ) :
      (ringSimplicialModule (p.stalkCommRing A)
        (Under.mk (p.stalkCommRingMap φ))).obj (op ⦋n⦌) ⟶
    (ModuleCat.extendScalars
        (p.stalkCommRingMap (standardAugmentation A (Under.mk φ) (op ⦋n⦌))).hom).obj
      (CommRingCat.KaehlerDifferential (pulledTerm φ p (op ⦋n⦌)).hom) :=
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

private theorem standardTermTensorIso_laws (n : ℕ) :
    standardTermTensorIsoHom φ p n ≫ standardTermTensorIsoInv φ p n = 𝟙 _ ∧
      standardTermTensorIsoInv φ p n ≫ standardTermTensorIsoHom φ p n = 𝟙 _ :=
  sorry

/-- Algebra-level comparison of simplicial tensor terms along `standardTermIso`. -/
private def standardTermTensorIso (n : ℕ) :
    (ModuleCat.extendScalars
        (p.stalkCommRingMap (standardAugmentation A (Under.mk φ) (op ⦋n⦌))).hom).obj
      (CommRingCat.KaehlerDifferential (pulledTerm φ p (op ⦋n⦌)).hom) ≅
      (ringSimplicialModule (p.stalkCommRing A)
        (Under.mk (p.stalkCommRingMap φ))).obj (op ⦋n⦌) where
  hom := standardTermTensorIsoHom φ p n
  inv := standardTermTensorIsoInv φ p n
  hom_inv_id := (standardTermTensorIso_laws φ p n).1
  inv_hom_id := (standardTermTensorIso_laws φ p n).2

private def derivationAddApp {X Y : Sheaf J CommRingCat.{u}} (ψ : X ⟶ Y)
    (U : Cᵒᵖ) :
    (Y.obj ⋙ forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat.{u}).obj U ⟶
      (relativeDifferentials ψ).val.presheaf.obj U :=
  AddCommGrpCat.ofHom (relativeDifferential ψ).d

private theorem derivationAddNatTrans_naturality {X Y : Sheaf J CommRingCat.{u}}
    (ψ : X ⟶ Y) {U V : Cᵒᵖ} (i : U ⟶ V) :
    (Y.obj ⋙ forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat.{u}).map i ≫
        derivationAddApp ψ V =
      derivationAddApp ψ U ≫ (relativeDifferentials ψ).val.presheaf.map i :=
  sorry

/-- Additive natural transformation underlying the universal relative derivation. -/
private def derivationAddNatTrans {X Y : Sheaf J CommRingCat.{u}} (ψ : X ⟶ Y) :
    Y.obj ⋙ forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat.{u} ⟶
      (relativeDifferentials ψ).val.presheaf where
  app := derivationAddApp ψ
  naturality _ _ i := derivationAddNatTrans_naturality ψ i

private def stalkDerivationFun {X Y : Sheaf J CommRingCat.{u}} (ψ : X ⟶ Y)
    (b : p.stalkCommRing Y) : p.moduleStalk Y (relativeDifferentials ψ) :=
  (p.presheafFiber.map (derivationAddNatTrans ψ))
    ((p.presheafFiberCompIso
      (forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat.{u})).inv.app Y.obj b)

private theorem differentialsStalkInv_laws {X Y : Sheaf J CommRingCat.{u}} (ψ : X ⟶ Y) :
    (∀ b b', stalkDerivationFun p ψ (b + b') =
      stalkDerivationFun p ψ b + stalkDerivationFun p ψ b') ∧
    (∀ b b', stalkDerivationFun p ψ (b * b') =
      b • stalkDerivationFun p ψ b' + b' • stalkDerivationFun p ψ b) ∧
    (∀ a, stalkDerivationFun p ψ (p.stalkCommRingMap ψ a) = 0) :=
  sorry

/-- The stalk of the universal derivation induces a map from differentials of the stalk map. -/
private def differentialsStalkInv {X Y : Sheaf J CommRingCat.{u}} (ψ : X ⟶ Y) :
    CommRingCat.KaehlerDifferential (p.stalkCommRingMap ψ) ⟶
      p.moduleStalk Y (relativeDifferentials ψ) :=
  (ModuleCat.Derivation.mk (stalkDerivationFun p ψ)
    (differentialsStalkInv_laws p ψ).1
    (differentialsStalkInv_laws p ψ).2.1
    (differentialsStalkInv_laws p ψ).2.2).desc

private def differentialsPresheafToSkyscraperApp {X Y : Sheaf J CommRingCat.{u}} (ψ : X ⟶ Y) (U : Cᵒᵖ) :
    ((relativeDifferentials' ψ.hom).presheaf).obj U ⟶ (p.skyscraperPresheaf
        ((forget₂ (ModuleCat.{u} (p.stalkCommRing Y)) AddCommGrpCat.{u}).obj
          (CommRingCat.KaehlerDifferential (p.stalkCommRingMap ψ)))).obj U :=
    Pi.lift (fun x ↦
      (forget₂ (ModuleCat.{u} (Y.obj.obj U)) AddCommGrpCat.{u}).map
        (CommRingCat.KaehlerDifferential.map
          (g' := p.toPresheafFiber U.unop x Y.obj)
          (p.toPresheafFiber_naturality ψ.hom U.unop x)))

private theorem differentialsPresheafToSkyscraper_naturality {X Y : Sheaf J CommRingCat.{u}} (ψ : X ⟶ Y) {U V : Cᵒᵖ} (i : U ⟶ V) :
    ((relativeDifferentials' ψ.hom).presheaf).map i ≫ differentialsPresheafToSkyscraperApp p ψ V =
      differentialsPresheafToSkyscraperApp p ψ U ≫ (p.skyscraperPresheaf
        ((forget₂ (ModuleCat.{u} (p.stalkCommRing Y)) AddCommGrpCat.{u}).obj
          (CommRingCat.KaehlerDifferential (p.stalkCommRingMap ψ)))).map i :=
  sorry

/-- Objectwise map from the presheaf of relative differentials to the skyscraper of Kahler
differentials of the stalk homomorphism. -/
private def differentialsPresheafToSkyscraper {X Y : Sheaf J CommRingCat.{u}} (ψ : X ⟶ Y) :
    (relativeDifferentials' ψ.hom).presheaf ⟶
      p.skyscraperPresheaf
        ((forget₂ (ModuleCat.{u} (p.stalkCommRing Y)) AddCommGrpCat.{u}).obj
          (CommRingCat.KaehlerDifferential (p.stalkCommRingMap ψ))) where
  app := differentialsPresheafToSkyscraperApp p ψ
  naturality _ _ i := differentialsPresheafToSkyscraper_naturality p ψ i

/-- Sheafification of the objectwise Kahler comparison, as a map of additive sheaves. -/
private def differentialsToSkyscraper {X Y : Sheaf J CommRingCat.{u}} (ψ : X ⟶ Y) :
    (toSheaf (ringSheaf J Y)).obj (relativeDifferentials ψ) ⟶
      p.skyscraperSheaf
        ((forget₂ (ModuleCat.{u} (p.stalkCommRing Y)) AddCommGrpCat.{u}).obj
          (CommRingCat.KaehlerDifferential (p.stalkCommRingMap ψ))) :=
  ((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ _).symm
    (differentialsPresheafToSkyscraper p ψ)

private def differentialsStalkHomFun {X Y : Sheaf J CommRingCat.{u}} (ψ : X ⟶ Y) :
    (p.moduleStalk Y (relativeDifferentials ψ)) → (CommRingCat.KaehlerDifferential (p.stalkCommRingMap ψ)) :=
        ConcreteCategory.hom
          (((p.skyscraperSheafAdjunction (A := AddCommGrpCat.{u})).homEquiv _ _).symm
            (differentialsToSkyscraper p ψ))

private theorem differentialsStalkHom_laws {X Y : Sheaf J CommRingCat.{u}} (ψ : X ⟶ Y) :
    (∀ a b, differentialsStalkHomFun p ψ (a + b) =
      differentialsStalkHomFun p ψ a + differentialsStalkHomFun p ψ b) ∧
    (∀ (r : p.stalkCommRing Y) m, differentialsStalkHomFun p ψ (r • m) =
      r • differentialsStalkHomFun p ψ m) :=
  sorry

/-- Forward comparison from the stalk of sheaf relative differentials to Kahler differentials
of the stalk homomorphism, induced by the universal derivation of the stalk map. -/
private def differentialsStalkHom {X Y : Sheaf J CommRingCat.{u}} (ψ : X ⟶ Y) :
    p.moduleStalk Y (relativeDifferentials ψ) ⟶
      CommRingCat.KaehlerDifferential (p.stalkCommRingMap ψ) :=
  ConcreteCategory.ofHom
    { toFun := differentialsStalkHomFun p ψ
      map_add' := (differentialsStalkHom_laws p ψ).1
      map_smul' := (differentialsStalkHom_laws p ψ).2 }

private theorem differentialsStalkIso_laws {X Y : Sheaf J CommRingCat.{u}} (ψ : X ⟶ Y) :
    differentialsStalkHom p ψ ≫ differentialsStalkInv p ψ = 𝟙 _ ∧
      differentialsStalkInv p ψ ≫ differentialsStalkHom p ψ = 𝟙 _ :=
  sorry

/-- The stalk of sheaf relative differentials is canonically the Kahler module of the stalk
homomorphism. -/
private def differentialsStalkIso {X Y : Sheaf J CommRingCat.{u}} (ψ : X ⟶ Y) :
    p.moduleStalk Y (relativeDifferentials ψ) ≅
      CommRingCat.KaehlerDifferential (p.stalkCommRingMap ψ) where
  hom := differentialsStalkHom p ψ
  inv := differentialsStalkInv p ψ
  hom_inv_id := (differentialsStalkIso_laws p ψ).1
  inv_hom_id := (differentialsStalkIso_laws p ψ).2

/-- Compatibility of commutative-ring stalk equivalences with a morphism of ring sheaves. -/
private theorem stalkRingEquiv_comp {O₂ O₃ : Sheaf J CommRingCat.{u}} (α : O₂ ⟶ O₃) :
    (p.stalkRingEquiv O₃).symm.toRingHom.comp (p.stalkCommRingMap α).hom =
      (p.presheafFiber.map (ringSheafMap α).hom).hom.comp
        (p.stalkRingEquiv O₂).symm.toRingHom :=
  sorry

private def restrictSheafModuleStalkHomFun {O₂ O₃ : Sheaf J CommRingCat.{u}} (α : O₂ ⟶ O₃)
    (M : SheafOfModules (ringSheaf J O₃)) :
    ((p.sheafModuleStalkFunctor (ringSheaf J O₂)).obj ((restrictionAlong α).obj M)) → ((ModuleCat.restrictScalars (p.presheafFiber.map (ringSheafMap α).hom).hom).obj
        ((p.sheafModuleStalkFunctor (ringSheaf J O₃)).obj M)) := id

private def restrictSheafModuleStalkInvFun {O₂ O₃ : Sheaf J CommRingCat.{u}} (α : O₂ ⟶ O₃)
    (M : SheafOfModules (ringSheaf J O₃)) :
    ((ModuleCat.restrictScalars (p.presheafFiber.map (ringSheafMap α).hom).hom).obj
        ((p.sheafModuleStalkFunctor (ringSheaf J O₃)).obj M)) → ((p.sheafModuleStalkFunctor (ringSheaf J O₂)).obj ((restrictionAlong α).obj M)) := id

private theorem restrictSheafModuleStalkIso_smul {O₂ O₃ : Sheaf J CommRingCat.{u}} (α : O₂ ⟶ O₃)
    (M : SheafOfModules (ringSheaf J O₃)) :
    (∀ (r : (p.presheafFiber (A := RingCat.{u})).obj (ringSheaf J O₂).obj) m, restrictSheafModuleStalkHomFun p α M (r • m) =
      r • restrictSheafModuleStalkHomFun p α M m) ∧
    (∀ (r : (p.presheafFiber (A := RingCat.{u})).obj (ringSheaf J O₂).obj) m, restrictSheafModuleStalkInvFun p α M (r • m) =
      r • restrictSheafModuleStalkInvFun p α M m) :=
  sorry

private def restrictSheafModuleStalkHom {O₂ O₃ : Sheaf J CommRingCat.{u}} (α : O₂ ⟶ O₃)
    (M : SheafOfModules (ringSheaf J O₃)) :
    ((p.sheafModuleStalkFunctor (ringSheaf J O₂)).obj ((restrictionAlong α).obj M)) ⟶ ((ModuleCat.restrictScalars (p.presheafFiber.map (ringSheafMap α).hom).hom).obj
        ((p.sheafModuleStalkFunctor (ringSheaf J O₃)).obj M)) :=
  ConcreteCategory.ofHom
    { toFun := restrictSheafModuleStalkHomFun p α M
      map_add' := fun _ _ ↦ rfl
      map_smul' := (restrictSheafModuleStalkIso_smul p α M).1 }

private def restrictSheafModuleStalkInv {O₂ O₃ : Sheaf J CommRingCat.{u}} (α : O₂ ⟶ O₃)
    (M : SheafOfModules (ringSheaf J O₃)) :
    ((ModuleCat.restrictScalars (p.presheafFiber.map (ringSheafMap α).hom).hom).obj
        ((p.sheafModuleStalkFunctor (ringSheaf J O₃)).obj M)) ⟶ ((p.sheafModuleStalkFunctor (ringSheaf J O₂)).obj ((restrictionAlong α).obj M)) :=
  ConcreteCategory.ofHom
    { toFun := restrictSheafModuleStalkInvFun p α M
      map_add' := fun _ _ ↦ rfl
      map_smul' := (restrictSheafModuleStalkIso_smul p α M).2 }

private theorem restrictSheafModuleStalkIso_laws {O₂ O₃ : Sheaf J CommRingCat.{u}} (α : O₂ ⟶ O₃)
    (M : SheafOfModules (ringSheaf J O₃)) :
    restrictSheafModuleStalkHom p α M ≫ restrictSheafModuleStalkInv p α M = 𝟙 _ ∧
      restrictSheafModuleStalkInv p α M ≫ restrictSheafModuleStalkHom p α M = 𝟙 _ :=
  sorry

/-- Restriction of scalars on module sheaves commutes with the ring-valued module stalk. -/
private def restrictSheafModuleStalkIso {O₂ O₃ : Sheaf J CommRingCat.{u}} (α : O₂ ⟶ O₃)
    (M : SheafOfModules (ringSheaf J O₃)) :
    (p.sheafModuleStalkFunctor (ringSheaf J O₂)).obj ((restrictionAlong α).obj M) ≅
      (ModuleCat.restrictScalars (p.presheafFiber.map (ringSheafMap α).hom).hom).obj
        ((p.sheafModuleStalkFunctor (ringSheaf J O₃)).obj M) where
  hom := restrictSheafModuleStalkHom p α M
  inv := restrictSheafModuleStalkInv p α M
  hom_inv_id := (restrictSheafModuleStalkIso_laws p α M).1
  inv_hom_id := (restrictSheafModuleStalkIso_laws p α M).2

/-- Restriction of scalars commutes with taking module stalks. -/
private def restrictStalkIso {O₂ O₃ : Sheaf J CommRingCat.{u}} (α : O₂ ⟶ O₃)
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

private def sheafificationStalkGermApp {O : Sheaf J CommRingCat.{u}}
    (F : PresheafOfModules (ringSheaf J O).obj) (U : Cᵒᵖ) :
    F.presheaf.obj U ⟶ (p.skyscraperPresheaf (p.presheafFiber.obj F.presheaf)).obj U :=
  Pi.lift (fun x ↦ p.toPresheafFiber U.unop x F.presheaf)

private theorem sheafificationStalkInv_naturality {O : Sheaf J CommRingCat.{u}}
    (F : PresheafOfModules (ringSheaf J O).obj) {U V : Cᵒᵖ} (i : U ⟶ V) :
    F.presheaf.map i ≫ sheafificationStalkGermApp p F V =
      sheafificationStalkGermApp p F U ≫
        (p.skyscraperPresheaf (p.presheafFiber.obj F.presheaf)).map i :=
  sorry

private def sheafificationStalkGerm {O : Sheaf J CommRingCat.{u}}
    (F : PresheafOfModules (ringSheaf J O).obj) :
    F.presheaf ⟶ p.skyscraperPresheaf (p.presheafFiber.obj F.presheaf) where
  app := sheafificationStalkGermApp p F
  naturality _ _ i := sheafificationStalkInv_naturality p F i

private def sheafificationStalkInvFun {O : Sheaf J CommRingCat.{u}}
    (F : PresheafOfModules (ringSheaf J O).obj) :
    (p.moduleStalk O
        ((PresheafOfModules.sheafification (𝟙 (ringSheaf J O).obj)).obj F)) → ((ModuleCat.restrictScalars (p.stalkRingEquiv O).symm.toRingHom).obj
        ((p.presheafModuleStalkFunctor (ringSheaf J O)).obj F)) :=
        ConcreteCategory.hom
          (((p.skyscraperSheafAdjunction (A := AddCommGrpCat.{u})).homEquiv _ _).symm
            (((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ _).symm
              (sheafificationStalkGerm p F)))

private theorem sheafificationStalkInv_laws {O : Sheaf J CommRingCat.{u}}
    (F : PresheafOfModules (ringSheaf J O).obj) :
    (∀ a b, sheafificationStalkInvFun p F (a + b) =
      sheafificationStalkInvFun p F a + sheafificationStalkInvFun p F b) ∧
    (∀ (r : p.stalkCommRing O) m, sheafificationStalkInvFun p F (r • m) =
      r • sheafificationStalkInvFun p F m) :=
  sorry

/-- The inverse of sheafification on module stalks, obtained by adjunction with the skyscraper
of the original presheaf stalk. -/
private def sheafificationStalkInv {O : Sheaf J CommRingCat.{u}}
    (F : PresheafOfModules (ringSheaf J O).obj) :
    p.moduleStalk O
        ((PresheafOfModules.sheafification (𝟙 (ringSheaf J O).obj)).obj F) ⟶
      (ModuleCat.restrictScalars (p.stalkRingEquiv O).symm.toRingHom).obj
        ((p.presheafModuleStalkFunctor (ringSheaf J O)).obj F) :=
  ConcreteCategory.ofHom
    { toFun := sheafificationStalkInvFun p F
      map_add' := (sheafificationStalkInv_laws p F).1
      map_smul' := (sheafificationStalkInv_laws p F).2 }

/-- The germ ring homomorphism from sections of a commutative ring sheaf to the stalk. -/
private def germHom {O : Sheaf J CommRingCat.{u}} (U : C) (x : p.fiber.obj U) :
    (ringSheaf J O).obj.obj (op U) →+* p.stalkCommRing O :=
  ((forget₂ CommRingCat RingCat.{u}).map (p.toPresheafFiber U x O.obj)).hom

private theorem germHom_naturality {O : Sheaf J CommRingCat.{u}}
    {U V : Cᵒᵖ} (i : U ⟶ V) (y : p.fiber.obj V.unop) :
    germHom p U.unop (p.fiber.map i.unop y) =
      (germHom p V.unop y).comp ((ringSheaf J O).obj.map i).hom :=
  sorry

/-- The value of the module skyscraper at one object of the site. -/
private def moduleSkyscraperObj {O : Sheaf J CommRingCat.{u}}
    (N : ModuleCat.{u} (p.stalkCommRing O)) (U : Cᵒᵖ) :
    ModuleCat ((ringSheaf J O).obj.obj U) :=
  ∏ᶜ fun x : p.fiber.obj U.unop ↦
    (ModuleCat.restrictScalars (germHom p U.unop x)).obj N

private def moduleSkyscraperMapFun {O : Sheaf J CommRingCat.{u}}
    (N : ModuleCat.{u} (p.stalkCommRing O)) {U V : Cᵒᵖ} (i : U ⟶ V) :
    (moduleSkyscraperObj p N U) → ((ModuleCat.restrictScalars ((ringSheaf J O).obj.map i).hom).obj
        (moduleSkyscraperObj p N V)) :=
  fun m ↦
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
                    (germHom_naturality p i y)).hom.app N))
              m))

private theorem moduleSkyscraperMap_laws {O : Sheaf J CommRingCat.{u}}
    (N : ModuleCat.{u} (p.stalkCommRing O)) {U V : Cᵒᵖ} (i : U ⟶ V) :
    (∀ a b, moduleSkyscraperMapFun p N i (a + b) =
      moduleSkyscraperMapFun p N i a + moduleSkyscraperMapFun p N i b) ∧
    (∀ (r : (ringSheaf J O).obj.obj U) m, moduleSkyscraperMapFun p N i (r • m) =
      r • moduleSkyscraperMapFun p N i m) :=
  sorry

/-- Restriction maps of the module skyscraper, as the product reindexing along the fiber. -/
private def moduleSkyscraperMap {O : Sheaf J CommRingCat.{u}}
    (N : ModuleCat.{u} (p.stalkCommRing O)) {U V : Cᵒᵖ} (i : U ⟶ V) :
    moduleSkyscraperObj p N U ⟶
      (ModuleCat.restrictScalars ((ringSheaf J O).obj.map i).hom).obj
        (moduleSkyscraperObj p N V) :=
  ConcreteCategory.ofHom
    { toFun := moduleSkyscraperMapFun p N i
      map_add' := (moduleSkyscraperMap_laws p N i).1
      map_smul' := (moduleSkyscraperMap_laws p N i).2 }

private theorem moduleSkyscraper_laws {O : Sheaf J CommRingCat.{u}}
    (N : ModuleCat.{u} (p.stalkCommRing O)) :
    (∀ U, moduleSkyscraperMap p N (𝟙 U) =
      (ModuleCat.restrictScalarsId' ((ringSheaf J O).obj.map (𝟙 U)).hom
        (congrArg RingCat.Hom.hom ((ringSheaf J O).obj.map_id U))).inv.app _) ∧
    (∀ {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W),
      moduleSkyscraperMap p N (i ≫ j) =
        moduleSkyscraperMap p N i ≫
          (ModuleCat.restrictScalars _).map (moduleSkyscraperMap p N j) ≫
          (ModuleCat.restrictScalarsComp'
            ((ringSheaf J O).obj.map i).hom ((ringSheaf J O).obj.map j).hom
            ((ringSheaf J O).obj.map (i ≫ j)).hom
            (congrArg RingCat.Hom.hom ((ringSheaf J O).obj.map_comp i j))).inv.app _) :=
  sorry

/-- Module-valued skyscraper presheaf attached to a stalk module at a site point. -/
private def moduleSkyscraper {O : Sheaf J CommRingCat.{u}}
    (N : ModuleCat.{u} (p.stalkCommRing O)) :
    PresheafOfModules (ringSheaf J O).obj where
  obj := moduleSkyscraperObj p N
  map := moduleSkyscraperMap p N
  map_id := (moduleSkyscraper_laws p N).1
  map_comp := (moduleSkyscraper_laws p N).2

private def moduleSkyscraperToAddApp {O : Sheaf J CommRingCat.{u}}
    (N : ModuleCat.{u} (p.stalkCommRing O)) (U : Cᵒᵖ) :
    ((PresheafOfModules.toPresheaf (ringSheaf J O).obj).obj (moduleSkyscraper p N)).obj U ⟶ (p.skyscraperPresheaf
        ((forget₂ (ModuleCat.{u} (p.stalkCommRing O)) AddCommGrpCat.{u}).obj N)).obj U :=
    Pi.lift fun x : p.fiber.obj U.unop ↦
      (forget₂ (ModuleCat ((ringSheaf J O).obj.obj U)) AddCommGrpCat.{u}).map
          (Pi.π (fun y : p.fiber.obj U.unop ↦
            (ModuleCat.restrictScalars (germHom p U.unop y)).obj N) x) ≫
        AddCommGrpCat.ofHom
          { toFun := id
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }

private theorem moduleSkyscraperToAdd_naturality {O : Sheaf J CommRingCat.{u}}
    (N : ModuleCat.{u} (p.stalkCommRing O))
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    ((PresheafOfModules.toPresheaf (ringSheaf J O).obj).obj (moduleSkyscraper p N)).map i ≫ moduleSkyscraperToAddApp p N V =
      moduleSkyscraperToAddApp p N U ≫ (p.skyscraperPresheaf
        ((forget₂ (ModuleCat.{u} (p.stalkCommRing O)) AddCommGrpCat.{u}).obj N)).map i :=
  sorry

/-- Forgetful comparison from the module skyscraper to the additive skyscraper. -/
private def moduleSkyscraperToAdd {O : Sheaf J CommRingCat.{u}}
    (N : ModuleCat.{u} (p.stalkCommRing O)) :
    (PresheafOfModules.toPresheaf (ringSheaf J O).obj).obj (moduleSkyscraper p N) ⟶
      p.skyscraperPresheaf
        ((forget₂ (ModuleCat.{u} (p.stalkCommRing O)) AddCommGrpCat.{u}).obj N) where
  app := moduleSkyscraperToAddApp p N
  naturality _ _ i := moduleSkyscraperToAdd_naturality p N i

private def toRestrictedExtendSkyscraperApp {O₂ O₃ : Sheaf J CommRingCat.{u}} (α : O₂ ⟶ O₃)
    (M : SheafOfModules (ringSheaf J O₂)) (U : Cᵒᵖ) :
    (M.val).presheaf.obj U ⟶ ((PresheafOfModules.pushforward (ringedSiteStructureMap α).hom).obj
        (moduleSkyscraper p
          ((ModuleCat.extendScalars (p.stalkCommRingMap α).hom).obj
            (p.moduleStalk O₂ M)))).presheaf.obj U :=
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

private theorem toRestrictedExtendSkyscraper_naturality {O₂ O₃ : Sheaf J CommRingCat.{u}} (α : O₂ ⟶ O₃)
    (M : SheafOfModules (ringSheaf J O₂))
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    (M.val).presheaf.map i ≫ toRestrictedExtendSkyscraperApp p α M V =
      toRestrictedExtendSkyscraperApp p α M U ≫ ((PresheafOfModules.pushforward (ringedSiteStructureMap α).hom).obj
        (moduleSkyscraper p
          ((ModuleCat.extendScalars (p.stalkCommRingMap α).hom).obj
            (p.moduleStalk O₂ M)))).presheaf.map i :=
  sorry

private def toRestrictedExtendSkyscraperAdd {O₂ O₃ : Sheaf J CommRingCat.{u}} (α : O₂ ⟶ O₃)
    (M : SheafOfModules (ringSheaf J O₂)) :
    (M.val).presheaf ⟶ ((PresheafOfModules.pushforward (ringedSiteStructureMap α).hom).obj
        (moduleSkyscraper p
          ((ModuleCat.extendScalars (p.stalkCommRingMap α).hom).obj
            (p.moduleStalk O₂ M)))).presheaf where
  app := toRestrictedExtendSkyscraperApp p α M
  naturality _ _ i := toRestrictedExtendSkyscraper_naturality p α M i

private theorem toRestrictedExtendSkyscraper_linearity {O₂ O₃ : Sheaf J CommRingCat.{u}} (α : O₂ ⟶ O₃)
    (M : SheafOfModules (ringSheaf J O₂))
    (U : Cᵒᵖ) (r : (ringSheaf J O₂).obj.obj U) (m : M.val.obj U) :
    (toRestrictedExtendSkyscraperAdd p α M).app U (r • m) =
      r • (toRestrictedExtendSkyscraperAdd p α M).app U m :=
  sorry

/-- A module sheaf maps to the skyscraper of the scalar extension of its stalk, after
restriction of scalars along a ring-sheaf homomorphism. -/
private def toRestrictedExtendSkyscraper {O₂ O₃ : Sheaf J CommRingCat.{u}} (α : O₂ ⟶ O₃)
    (M : SheafOfModules (ringSheaf J O₂)) :
    M.val ⟶
      (PresheafOfModules.pushforward (ringedSiteStructureMap α).hom).obj
        (moduleSkyscraper p
          ((ModuleCat.extendScalars (p.stalkCommRingMap α).hom).obj
            (p.moduleStalk O₂ M))) :=
  PresheafOfModules.homMk (toRestrictedExtendSkyscraperAdd p α M)
    (toRestrictedExtendSkyscraper_linearity p α M)

private def pullbackStalkToExtendFun {O₂ O₃ : Sheaf J CommRingCat.{u}} (α : O₂ ⟶ O₃)
    (M : SheafOfModules (ringSheaf J O₂)) :
    ((ModuleCat.restrictScalars (p.stalkRingEquiv O₃).symm.toRingHom).obj
      ((p.presheafModuleStalkFunctor (ringSheaf J O₃)).obj
        ((PresheafOfModules.pullback (ringedSiteStructureMap α).hom).obj M.val))) → ((ModuleCat.extendScalars (p.stalkCommRingMap α).hom).obj (p.moduleStalk O₂ M)) :=
  ConcreteCategory.hom
          (p.skyscraperPresheafHomEquiv.symm
            ((PresheafOfModules.toPresheaf (ringSheaf J O₃).obj).map
                ((PresheafOfModules.pullbackPushforwardAdjunction
                    (ringedSiteStructureMap α).hom).homEquiv _ _ |>.symm
                  (toRestrictedExtendSkyscraper p α M)) ≫
              moduleSkyscraperToAdd p
                ((ModuleCat.extendScalars (p.stalkCommRingMap α).hom).obj
                  (p.moduleStalk O₂ M))))

private theorem pullbackStalkToExtend_laws {O₂ O₃ : Sheaf J CommRingCat.{u}} (α : O₂ ⟶ O₃)
    (M : SheafOfModules (ringSheaf J O₂)) :
    (∀ a b, pullbackStalkToExtendFun p α M (a + b) =
      pullbackStalkToExtendFun p α M a + pullbackStalkToExtendFun p α M b) ∧
    (∀ (r : p.stalkCommRing O₃) m, pullbackStalkToExtendFun p α M (r • m) =
      r • pullbackStalkToExtendFun p α M m) :=
  sorry

/-- The canonical comparison from the presheaf-module stalk of a pullback to scalar extension
of the original module stalk. -/
private def pullbackStalkToExtend {O₂ O₃ : Sheaf J CommRingCat.{u}} (α : O₂ ⟶ O₃)
    (M : SheafOfModules (ringSheaf J O₂)) :
    (ModuleCat.restrictScalars (p.stalkRingEquiv O₃).symm.toRingHom).obj
      ((p.presheafModuleStalkFunctor (ringSheaf J O₃)).obj
        ((PresheafOfModules.pullback (ringedSiteStructureMap α).hom).obj M.val)) ⟶
      (ModuleCat.extendScalars (p.stalkCommRingMap α).hom).obj (p.moduleStalk O₂ M) :=
  ConcreteCategory.ofHom
    { toFun := pullbackStalkToExtendFun p α M
      map_add' := (pullbackStalkToExtend_laws p α M).1
      map_smul' := (pullbackStalkToExtend_laws p α M).2 }

private def extendAlongStalkHom (n : ℕ) :
    (p.moduleStalk B ((simplicialModule A (Under.mk φ)).obj (op ⦋n⦌))) ⟶ ((ModuleCat.extendScalars
          (p.stalkCommRingMap (standardAugmentation A (Under.mk φ) (op ⦋n⦌))).hom).obj
        (p.moduleStalk (standardTerm A (Under.mk φ) (op ⦋n⦌)).right
          (relativeDifferentials (standardTerm A (Under.mk φ) (op ⦋n⦌)).hom))) :=
  let α := standardAugmentation A (Under.mk φ) (op ⦋n⦌)
  let Ωn := relativeDifferentials (standardTerm A (Under.mk φ) (op ⦋n⦌)).hom
  (p.moduleStalkFunctor B).map
          ((SheafOfModules.ChangeOfRings.pullbackIso (ringSheafMap α)).inv.app Ωn ≫
            (SheafOfModules.pullbackIso (ringedSiteStructureMap α)).hom.app Ωn) ≫
        sheafificationStalkInv p
          ((PresheafOfModules.pullback (ringedSiteStructureMap α).hom).obj Ωn.val) ≫
        pullbackStalkToExtend p α Ωn

private def extendAlongStalkInv (n : ℕ) :
    ((ModuleCat.extendScalars
          (p.stalkCommRingMap (standardAugmentation A (Under.mk φ) (op ⦋n⦌))).hom).obj
        (p.moduleStalk (standardTerm A (Under.mk φ) (op ⦋n⦌)).right
          (relativeDifferentials (standardTerm A (Under.mk φ) (op ⦋n⦌)).hom))) ⟶ (p.moduleStalk B ((simplicialModule A (Under.mk φ)).obj (op ⦋n⦌))) :=
  let α := standardAugmentation A (Under.mk φ) (op ⦋n⦌)
  let Ωn := relativeDifferentials (standardTerm A (Under.mk φ) (op ⦋n⦌)).hom
  ((ModuleCat.extendRestrictScalarsAdj (p.stalkCommRingMap α).hom).homEquiv
      (p.moduleStalk (standardTerm A (Under.mk φ) (op ⦋n⦌)).right Ωn)
      (p.moduleStalk B ((simplicialModule A (Under.mk φ)).obj (op ⦋n⦌)))).symm
      ((p.moduleStalkFunctor (standardTerm A (Under.mk φ) (op ⦋n⦌)).right).map
          ((SheafOfModules.ChangeOfRings.extendRestrictAdjunction (ringSheafMap α)).unit.app Ωn) ≫
        (restrictStalkIso p α ((simplicialModule A (Under.mk φ)).obj (op ⦋n⦌))).hom)

private theorem extendAlongStalkIso_laws (n : ℕ) :
    extendAlongStalkHom φ p n ≫ extendAlongStalkInv φ p n = 𝟙 _ ∧
      extendAlongStalkInv φ p n ≫ extendAlongStalkHom φ p n = 𝟙 _ :=
  sorry

/-- Stalk of a sheaf tensor term versus scalar extension of the stalk of relative
differentials. -/
private def extendAlongStalkIso (n : ℕ) :
    p.moduleStalk B ((simplicialModule A (Under.mk φ)).obj (op ⦋n⦌)) ≅
      (ModuleCat.extendScalars
          (p.stalkCommRingMap (standardAugmentation A (Under.mk φ) (op ⦋n⦌))).hom).obj
        (p.moduleStalk (standardTerm A (Under.mk φ) (op ⦋n⦌)).right
          (relativeDifferentials (standardTerm A (Under.mk φ) (op ⦋n⦌)).hom)) where
  hom := extendAlongStalkHom φ p n
  inv := extendAlongStalkInv φ p n
  hom_inv_id := (extendAlongStalkIso_laws φ p n).1
  inv_hom_id := (extendAlongStalkIso_laws φ p n).2

/-- Degreewise comparison of the stalk of a sheaf simplicial tensor term with the algebra
simplicial tensor term of the stalk homomorphism. -/
@[no_expose] def termIso (n : ℕ) :
    p.moduleStalk B ((simplicialModule A (Under.mk φ)).obj (op ⦋n⦌)) ≅
      (ringSimplicialModule (p.stalkCommRing A)
        (Under.mk (p.stalkCommRingMap φ))).obj (op ⦋n⦌) :=
  (extendAlongStalkIso φ p n).trans
    (((ModuleCat.extendScalars
          (p.stalkCommRingMap (standardAugmentation A (Under.mk φ) (op ⦋n⦌))).hom).mapIso
        (differentialsStalkIso p (standardTerm A (Under.mk φ) (op ⦋n⦌)).hom)).trans
      (standardTermTensorIso φ p n))

private theorem appIso_pos_laws (k : ℕ) :
    (0 : (source φ p).X (Int.ofNat k.succ) ⟶ (target φ p).X (Int.ofNat k.succ)) ≫
      (0 : (target φ p).X (Int.ofNat k.succ) ⟶ (source φ p).X (Int.ofNat k.succ)) = 𝟙 _ ∧
    (0 : (target φ p).X (Int.ofNat k.succ) ⟶ (source φ p).X (Int.ofNat k.succ)) ≫
      (0 : (source φ p).X (Int.ofNat k.succ) ⟶ (target φ p).X (Int.ofNat k.succ)) = 𝟙 _ :=
  sorry

/-- Degreewise comparison of the stalk of `L(φ)` with `L(B_p / A_p)`. -/
private def appIso : ∀ n : ℤ, (source φ p).X n ≅ (target φ p).X n
  | Int.ofNat (Nat.succ k) =>
      { hom := (0 : (source φ p).X (Int.ofNat k.succ) ⟶ (target φ p).X (Int.ofNat k.succ))
        inv := (0 : (target φ p).X (Int.ofNat k.succ) ⟶ (source φ p).X (Int.ofNat k.succ))
        hom_inv_id := (appIso_pos_laws φ p k).1
        inv_hom_id := (appIso_pos_laws φ p k).2 }
  | (0 : ℤ) =>
      (sourceXIso φ p 0).trans ((termIso φ p 0).trans (targetXIso φ p 0).symm)
  | Int.negSucc k =>
      (sourceXIso φ p k.succ).trans
        ((termIso φ p k.succ).trans (targetXIso φ p k.succ).symm)

private theorem iso_comm (i j : ℤ) (h : (ComplexShape.up ℤ).Rel i j) :
    (appIso φ p i).hom ≫ (target φ p).d i j =
      (source φ p).d i j ≫ (appIso φ p j).hom :=
  sorry

/-- The canonical identification `(L(φ))_p ≅ L(B_p / A_p)` of cochain complexes of
`B_p`-modules. -/
@[no_expose] def iso : source φ p ≅ target φ p :=
  Hom.isoOfComponents (appIso φ p) (iso_comm φ p)

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
