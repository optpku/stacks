/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.StandardTriangle
public import ReasLib.RingTheory.CotangentComplex.Functoriality
public import ReasLib.AlgebraicTopology.SimplicialObject.ModuleCochain
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Comparison of standard and tensor polynomial resolutions

Coefficient change and tensor inclusion compare the standard resolution with
tensor base changes of standard resolutions. Their differential complexes are
identified by the resulting quasi-isomorphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialObject
open AlgebraicTopology HomologicalComplex Algebra Algebra.PolynomialSite
open CommAlgCat.Over.Polynomial.Site
open CommRingCat.Under.CotangentComplex
open scoped TensorProduct

noncomputable section

universe u q

set_option backward.privateInPublic true

namespace Algebra.CotangentComplex

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

private def relativeQ (X : PolynomialTower A B C) : CommAlgCat X.P :=
  @CommAlgCat.of X.P _ X.Q _ X.algebraPQ

private def relativeB (X : PolynomialTower A B C) : CommAlgCat X.P :=
  @CommAlgCat.of X.P _ B _ X.toB.hom.toRingHom.toAlgebra

open CategoryTheory.CommRingCat.Under.PolynomialResolution
open CommRingCat.Under.FreeAlgebra

private theorem freeAlgebraRightHom_naturality {R S : CommRingCat.{u}}
    {E F E' F' : Type u} (α : R ⟶ S) (a : E ⟶ F) (b : E' ⟶ F')
    (x : E → E') (y : F → F') (h : ∀ e, y (a e) = b (x e)) :
    (CommRingCat.Under.FreeAlgebra.map R a).right ≫ freeAlgebraRightHom α y =
      freeAlgebraRightHom α x ≫ (CommRingCat.Under.FreeAlgebra.map S b).right := by
  have ha : (CommRingCat.Under.FreeAlgebra.map R a).right ≫ (toPolynomial R F).right =
      (toPolynomial R E).right ≫ (polynomialMap R a).right :=
    congrArg (fun f ↦ f.right) (toPolynomial_naturality R a)
  have hb : (polynomialMap S b).right ≫ (fromPolynomial S F').right =
      (fromPolynomial S E').right ≫ (CommRingCat.Under.FreeAlgebra.map S b).right :=
    congrArg (fun f ↦ f.right) (fromPolynomial_naturality S b)
  have hp : (polynomialMap R a).right ≫ CommRingCat.ofHom (mvPolynomialRingHom α.hom y) =
      CommRingCat.ofHom (mvPolynomialRingHom α.hom x) ≫ (polynomialMap S b).right := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    change MvPolynomial.rename y (MvPolynomial.map α.hom (MvPolynomial.rename a p)) =
      MvPolynomial.rename b (MvPolynomial.rename x (MvPolynomial.map α.hom p))
    simp only [MvPolynomial.map_rename, MvPolynomial.rename_rename]
    exact congrArg (fun f : E → F' ↦ MvPolynomial.rename f (MvPolynomial.map α.hom p))
      (funext h)
  calc
    _ = (toPolynomial R E).right ≫
        ((polynomialMap R a).right ≫ CommRingCat.ofHom (mvPolynomialRingHom α.hom y)) ≫
          (fromPolynomial S F').right := by
      dsimp only [freeAlgebraRightHom]
      rw [← Category.assoc, ← Category.assoc, ha]
      simp only [Category.assoc]
    _ = (toPolynomial R E).right ≫ CommRingCat.ofHom (mvPolynomialRingHom α.hom x) ≫
        (fromPolynomial S E').right ≫ (CommRingCat.Under.FreeAlgebra.map S b).right := by
      rw [hp]
      exact (congrArg (fun k ↦ (toPolynomial R E).right ≫ k)
        (Category.assoc (CommRingCat.ofHom (mvPolynomialRingHom α.hom x))
          (polynomialMap S b).right (fromPolynomial S F').right)).trans
        (congrArg (fun k ↦ (toPolynomial R E).right ≫
          CommRingCat.ofHom (mvPolynomialRingHom α.hom x) ≫ k) hb)
    _ = _ := by simp only [freeAlgebraRightHom, Category.assoc]

private theorem iterateRightHom_naturality {R S : CommRingCat.{u}}
    {X Y : Under R} {X' Y' : Under S} (α : R ⟶ S) (f : X ⟶ Y) (g : X' ⟶ Y')
    (β : X.right ⟶ X'.right) (γ : Y.right ⟶ Y'.right)
    (h : f.right ≫ γ = β ≫ g.right) (k : ℕ) :
    ((Endofunctor.iterate (CategoryTheory.CommRingCat.Under.PolynomialResolution.functor R) k).map f).right ≫
        iterateRightHom α γ k =
      iterateRightHom α β k ≫
        ((Endofunctor.iterate (CategoryTheory.CommRingCat.Under.PolynomialResolution.functor S) k).map g).right := by
  induction k with
  | zero => exact h
  | succ k ih =>
    apply freeAlgebraRightHom_naturality
    intro e
    exact congrArg (fun f ↦ f e) ih

/-- Coefficient change commutes with functoriality of standard resolutions. -/
private theorem functorialitySquare_comm (n : SimplexCategoryᵒᵖ) :
    (standardTermRightHom (B := (CommRingCat.of A).mkUnder C)
      (B' := (CommRingCat.of B).mkUnder C)
      (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (RingHom.id C)) n).hom.comp
        (functorialityApp A B C n).hom.toRingHom =
    (functorialityApp B B C n).hom.toRingHom.comp
      (standardTermRightHom (B := (CommRingCat.of A).mkUnder B)
        (B' := (CommRingCat.of B).mkUnder B)
        (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (RingHom.id B)) n).hom :=
  by
    exact congrArg (fun f ↦ f.hom)
      (iterateRightHom_naturality (CommRingCat.ofHom (algebraMap A B))
        (underHom A B C) (underHom B B C)
        (CommRingCat.ofHom (RingHom.id B)) (CommRingCat.ofHom (RingHom.id C))
        (by rfl) (n.unop.len + 1))

private abbrev algebraPOnBarR (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    Algebra ((triple A B C n h_inj).P) (barQ B B C n h_inj) :=
  ((algebraMap B (barQ B B C n h_inj)).comp
    ((standardHom A B).app n).hom.toRingHom).toAlgebra

private def targetOverP (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) : CommAlgCat ((triple A B C n h_inj).P) :=
  @CommAlgCat.of ((triple A B C n h_inj).P) _ (barQ B B C n h_inj) _
    (algebraPOnBarR A B C n h_inj)

private def tensorLeftRingHom (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    standardQ A C n →+* barQ B B C n h_inj :=
  (Algebra.TensorProduct.includeLeftRingHom :
    relativeQ B B C (triple B B C n h_inj) →+*
      relativeQ B B C (triple B B C n h_inj) ⊗[(triple B B C n h_inj).P]
        relativeB B B C (triple B B C n h_inj)).comp
    (standardTermRightHom (B := (CommRingCat.of A).mkUnder C)
      (B' := (CommRingCat.of B).mkUnder C)
      (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (RingHom.id C)) n).hom

/-- The coefficient-changing tensor inclusion respects the source standard algebra. -/
private theorem barQToBarRAlg_left_commutes (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) (p : (triple A B C n h_inj).P) :
    tensorLeftRingHom A B C n h_inj
      (algebraMap ((triple A B C n h_inj).P) (relativeQ A B C (triple A B C n h_inj)) p) =
        algebraMap ((triple A B C n h_inj).P) (targetOverP A B C n h_inj) p :=
  by
    let p' := (standardTermRightHom (B := (CommRingCat.of A).mkUnder B)
      (B' := (CommRingCat.of B).mkUnder B)
      (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (RingHom.id B)) n).hom p
    have hpq := RingHom.congr_fun (functorialitySquare_comm A B C n) p
    have hpb := RingHom.congr_fun
      (standardTermRightHom_comp_augmentation
        (B := (CommRingCat.of A).mkUnder B)
        (B' := (CommRingCat.of B).mkUnder B)
        (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (RingHom.id B))
        (by ext a; rfl) n) p
    simp only [RingHom.comp_apply] at hpq hpb
    change (show relativeQ B B C (triple B B C n h_inj) from _) ⊗ₜ[_]
      (1 : relativeB B B C (triple B B C n h_inj)) =
        (1 : relativeQ B B C (triple B B C n h_inj)) ⊗ₜ[_]
          (show relativeB B B C (triple B B C n h_inj) from _)
    exact (congrArg (fun q : relativeQ B B C (triple B B C n h_inj) ↦
      q ⊗ₜ[_] (1 : relativeB B B C (triple B B C n h_inj))) hpq).trans
      ((Algebra.TensorProduct.tmul_one_eq_one_tmul
      (R := (triple B B C n h_inj).P)
      (A := relativeQ B B C (triple B B C n h_inj))
      (B := relativeB B B C (triple B B C n h_inj)) p').trans
        (congrArg (fun b : relativeB B B C (triple B B C n h_inj) ↦
          (1 : relativeQ B B C (triple B B C n h_inj)) ⊗ₜ[_] b) hpb.symm))

private def tensorLeft (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    relativeQ A B C (triple A B C n h_inj) →ₐ[(triple A B C n h_inj).P]
      targetOverP A B C n h_inj :=
  { tensorLeftRingHom A B C n h_inj with
    commutes' := barQToBarRAlg_left_commutes A B C n h_inj }

/-- The right tensor inclusion respects the augmentation of the source standard algebra. -/
private theorem barQToBarRAlg_right_commutes (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) (p : (triple A B C n h_inj).P) :
    algebraMap B (barQ B B C n h_inj)
      (algebraMap ((triple A B C n h_inj).P) (relativeB A B C (triple A B C n h_inj)) p) =
        algebraMap ((triple A B C n h_inj).P) (targetOverP A B C n h_inj) p :=
  rfl

private def tensorRight (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    relativeB A B C (triple A B C n h_inj) →ₐ[(triple A B C n h_inj).P]
      targetOverP A B C n h_inj :=
  { (algebraMap B (barQ B B C n h_inj)) with
    commutes' := barQToBarRAlg_right_commutes A B C n h_inj }

private def tensorComparisonRingHom (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    barQ A B C n h_inj →+* barQ B B C n h_inj :=
  (Algebra.TensorProduct.productMap (tensorLeft A B C n h_inj)
    (tensorRight A B C n h_inj)).toRingHom

/-- The tensor comparison is linear for the canonical right action of the intermediate ring. -/
private theorem barQToBarRAlg_commutes (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) (b : B) :
    tensorComparisonRingHom A B C n h_inj (algebraMap B (barQ A B C n h_inj) b) =
      algebraMap B (barQ B B C n h_inj) b :=
  by
    change tensorLeft A B C n h_inj 1 * tensorRight A B C n h_inj b = _
    rw [map_one, one_mul]
    rfl

/-- Coefficient change and the identity on the right factor induce a map of tensor algebras. -/
def barQToBarRAlg (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    (barQOver A B C n h_inj).obj.left →ₐ[B] (barQOver B B C n h_inj).obj.left :=
  { tensorComparisonRingHom A B C n h_inj with
    commutes' := barQToBarRAlg_commutes A B C n h_inj }

/-- The tensor comparison changes coefficients in the left factor and fixes the right factor. -/
theorem barQToBarRAlg_tmul (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C))
    (x : relativeQ A B C (triple A B C n h_inj))
    (b : relativeB A B C (triple A B C n h_inj)) :
    barQToBarRAlg A B C n h_inj (x ⊗ₜ[(triple A B C n h_inj).P] b) =
      (show relativeQ B B C (triple B B C n h_inj) from
        (standardTermRightHom (B := (CommRingCat.of A).mkUnder C)
          (B' := (CommRingCat.of B).mkUnder C)
          (CommRingCat.ofHom (algebraMap A B))
          (CommRingCat.ofHom (RingHom.id C)) n).hom x) ⊗ₜ[(triple B B C n h_inj).P]
        (show relativeB B B C (triple B B C n h_inj) from b) := by
  change (_ ⊗ₜ[(triple B B C n h_inj).P] (1 : relativeB B B C (triple B B C n h_inj))) *
    ((1 : relativeQ B B C (triple B B C n h_inj)) ⊗ₜ[(triple B B C n h_inj).P] _) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The over-`C` triangle of `barQToBarRAlg`. -/
private theorem barQToBarROver_w (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    CommAlgCat.ofHom (barQToBarRAlg A B C n h_inj) ≫ (barQOver B B C n h_inj).obj.hom =
      (barQOver A B C n h_inj).obj.hom :=
  by
    apply CommAlgCat.hom_ext
    apply AlgHom.coe_ringHom_injective
    apply Algebra.TensorProduct.ringHom_ext
    · apply RingHom.ext
      intro x
      change (barQOver B B C n h_inj).obj.hom.hom
          (barQToBarRAlg A B C n h_inj (x ⊗ₜ[_] 1)) = _
      rw [barQToBarRAlg_tmul]
      have h := RingHom.congr_fun
        (standardTermRightHom_comp_augmentation
          (B := (CommRingCat.of A).mkUnder C)
          (B' := (CommRingCat.of B).mkUnder C)
          (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (RingHom.id C))
          (by ext a; exact (IsScalarTower.algebraMap_apply A B C a).symm) n) x
      change (show C from ((standardHom B C).app n).hom
          ((standardTermRightHom (B := (CommRingCat.of A).mkUnder C)
            (B' := (CommRingCat.of B).mkUnder C)
            (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (RingHom.id C)) n).hom x)) *
            algebraMap B C 1 = (show C from ((standardHom A C).app n).hom x) * algebraMap B C 1
      exact congrArg (fun c : C ↦ c * algebraMap B C 1) h.symm
    · apply RingHom.ext
      intro b
      change (barQOver B B C n h_inj).obj.hom.hom
          (barQToBarRAlg A B C n h_inj (1 ⊗ₜ[_] b)) = _
      rw [barQToBarRAlg_tmul]
      change (show C from ((standardHom B C).app n).hom
          ((standardTermRightHom (B := (CommRingCat.of A).mkUnder C)
            (B' := (CommRingCat.of B).mkUnder C)
            (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (RingHom.id C)) n).hom 1)) *
            algebraMap B C b = (show C from ((standardHom A C).app n).hom 1) * algebraMap B C b
      simp

/-- The morphism of polynomial `B`-algebras over `C` from `Q̄_n` to `R̄_n`. -/
def barQToBarROver (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    barQOver A B C n h_inj ⟶ barQOver B B C n h_inj :=
  ObjectProperty.homMk
    (Over.homMk (CommAlgCat.ofHom (barQToBarRAlg A B C n h_inj))
      (barQToBarROver_w A B C n h_inj))

private theorem coefficientChange_naturality {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    (standardTermRightHom (B := (CommRingCat.of A).mkUnder C)
      (B' := (CommRingCat.of B).mkUnder C)
      (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (RingHom.id C)) m).hom.comp
        ((standardAugmented A C).left.map φ).hom.toRingHom =
      ((standardAugmented B C).left.map φ).hom.toRingHom.comp
        (standardTermRightHom (B := (CommRingCat.of A).mkUnder C)
          (B' := (CommRingCat.of B).mkUnder C)
          (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (RingHom.id C)) n).hom := by
  let F := functorialityMap (B := (CommRingCat.of A).mkUnder C)
    (B' := (CommRingCat.of B).mkUnder C)
    (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (RingHom.id C))
    (by ext a; exact (IsScalarTower.algebraMap_apply A B C a).symm)
  have h :
      (F.app m).right.hom.comp
          ((((evaluation (CommRingCat.of A)).obj ((CommRingCat.of A).mkUnder C)).left.map φ).right.hom) =
        ((((evaluation (CommRingCat.of B)).obj ((CommRingCat.of B).mkUnder C)).left.map φ).right.hom).comp
          (F.app n).right.hom :=
    congrArg (fun f ↦ f.right.hom) (F.naturality φ)
  simp only [F, functorialityMap_app_right] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The canonical simplicial `B`-algebra map `Q̄_• ⟶ R̄_•`. -/
def barQToBarR (h_inj : Function.Injective (algebraMap B C)) :
    barQSimplicial A B C h_inj ⟶ barQSimplicial B B C h_inj where
  app n := (barQToBarROver A B C n h_inj).hom.left
  naturality n m φ := by
    apply CommAlgCat.hom_ext
    apply AlgHom.coe_ringHom_injective
    apply Algebra.TensorProduct.ringHom_ext
    · apply RingHom.ext
      intro x
      change barQToBarRAlg A B C m h_inj
          (((Algebra.PolynomialTower.forgetToOverB A B C).map
            (tripleMap A B C φ h_inj)).hom.left.hom (x ⊗ₜ[_] 1)) =
        ((Algebra.PolynomialTower.forgetToOverB B B C).map
          (tripleMap B B C φ h_inj)).hom.left.hom
            (barQToBarRAlg A B C n h_inj (x ⊗ₜ[_] 1))
      rw [Algebra.PolynomialTower.forgetToOverB_map_tmul,
        barQToBarRAlg_tmul, barQToBarRAlg_tmul,
        Algebra.PolynomialTower.forgetToOverB_map_tmul]
      exact congrArg (fun q : relativeQ B B C (triple B B C m h_inj) ↦
        q ⊗ₜ[_] (1 : relativeB B B C (triple B B C m h_inj)))
        (RingHom.congr_fun (coefficientChange_naturality A B C φ) x)
    · apply RingHom.ext
      intro b
      change barQToBarRAlg A B C m h_inj
          (((Algebra.PolynomialTower.forgetToOverB A B C).map
            (tripleMap A B C φ h_inj)).hom.left.hom (1 ⊗ₜ[_] b)) =
        ((Algebra.PolynomialTower.forgetToOverB B B C).map
          (tripleMap B B C φ h_inj)).hom.left.hom
            (barQToBarRAlg A B C n h_inj (1 ⊗ₜ[_] b))
      rw [Algebra.PolynomialTower.forgetToOverB_map_tmul,
        barQToBarRAlg_tmul, barQToBarRAlg_tmul,
        Algebra.PolynomialTower.forgetToOverB_map_tmul]
      simp

/-- Components of `barQToBarR` are the left morphisms of `barQToBarROver`. -/
theorem barQToBarR_app (h_inj : Function.Injective (algebraMap B C))
    (n : SimplexCategoryᵒᵖ) :
    (barQToBarR A B C h_inj).app n = (barQToBarROver A B C n h_inj).hom.left :=
  rfl

/-- The polynomial `B`-algebra arrow `R_n ⟶ C` of the standard resolution. -/
private abbrev standardROver (n : SimplexCategoryᵒᵖ) : PolynomialOver B C :=
  (asPolynomialSimplicial (standardHom B C) (standard_isPolynomial B C)).obj n

/-- The left tensor inclusion respects the canonical base-ring actions. -/
private theorem standardToBarRAlg_commutes (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) (b : B) :
    (Algebra.TensorProduct.includeLeftRingHom :
      relativeQ B B C (triple B B C n h_inj) →+*
        relativeQ B B C (triple B B C n h_inj) ⊗[(triple B B C n h_inj).P]
          relativeB B B C (triple B B C n h_inj))
      (algebraMap B (standardROver B C n).obj.left b) =
        algebraMap B (barQ B B C n h_inj) b :=
  by
    have hpq := (functorialityApp B B C n).hom.commutes b
    have hpb := ((standardHom B B).app n).hom.commutes b
    change (algebraMap B (standardQ B C n) b) ⊗ₜ[(triple B B C n h_inj).P]
      (1 : relativeB B B C (triple B B C n h_inj)) =
        (1 : relativeQ B B C (triple B B C n h_inj)) ⊗ₜ[_]
          (show relativeB B B C (triple B B C n h_inj) from b)
    rw [← hpq]
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul
      (R := (triple B B C n h_inj).P)
      (A := relativeQ B B C (triple B B C n h_inj))
      (B := relativeB B B C (triple B B C n h_inj))
      (algebraMap B (standardP B B n) b)).trans
        (congrArg (fun b : relativeB B B C (triple B B C n h_inj) ↦
          (1 : relativeQ B B C (triple B B C n h_inj)) ⊗ₜ[_] b) hpb)

/-- The standard algebra maps to its tensor base change by the left tensor inclusion. -/
def standardToBarRAlg (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    (standardROver B C n).obj.left →ₐ[B] (barQOver B B C n h_inj).obj.left :=
  { (Algebra.TensorProduct.includeLeftRingHom :
      relativeQ B B C (triple B B C n h_inj) →+*
        relativeQ B B C (triple B B C n h_inj) ⊗[(triple B B C n h_inj).P]
          relativeB B B C (triple B B C n h_inj)) with
    commutes' := standardToBarRAlg_commutes B C n h_inj }

/-- The standard-to-tensor comparison sends an element to its tensor with one. -/
theorem standardToBarRAlg_apply (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C))
    (x : (standardROver B C n).obj.left) :
    standardToBarRAlg B C n h_inj x =
      (show relativeQ B B C (triple B B C n h_inj) from x) ⊗ₜ[(triple B B C n h_inj).P]
        (1 : relativeB B B C (triple B B C n h_inj)) := rfl

/-- The left tensor inclusion commutes with the augmentations. -/
private theorem standardToBarROver_w (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    (CommAlgCat.ofHom (X := (standardROver B C n).obj.left)
      (Y := (barQOver B B C n h_inj).obj.left) (standardToBarRAlg B C n h_inj)) ≫ (barQOver B B C n h_inj).obj.hom =
      (standardROver B C n).obj.hom :=
  by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    change (show C from ((standardHom B C).app n).hom x) * algebraMap B C 1 =
      (show C from ((standardHom B C).app n).hom x)
    rw [map_one, mul_one]

/-- The morphism of polynomial `B`-algebras over `C` from `R_n` to `R̄_n`. -/
def standardToBarROver (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    standardROver B C n ⟶ barQOver B B C n h_inj :=
  ObjectProperty.homMk
    (Over.homMk ((CommAlgCat.ofHom (X := (standardROver B C n).obj.left)
      (Y := (barQOver B B C n h_inj).obj.left) (standardToBarRAlg B C n h_inj)))
      (standardToBarROver_w B C n h_inj))

/-- The simplicial `B`-algebra map `R_• ⟶ R̄_•`. -/
def standardToBarR (h_inj : Function.Injective (algebraMap B C)) :
    (standardAugmented B C).left ⟶ barQSimplicial B B C h_inj where
  app n := (standardToBarROver B C n h_inj).hom.left
  naturality n m φ := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    change standardToBarRAlg B C m h_inj ((standardAugmented B C).left.map φ x) =
      ((Algebra.PolynomialTower.forgetToOverB B B C).map
        (tripleMap B B C φ h_inj)).hom.left.hom
          (standardToBarRAlg B C n h_inj x)
    rw [standardToBarRAlg_apply, standardToBarRAlg_apply]
    exact (Algebra.PolynomialTower.forgetToOverB_map_tmul
      (tripleMap B B C φ h_inj) x 1).symm

/-- Components of `standardToBarR` are the left morphisms of `standardToBarROver`. -/
theorem standardToBarR_app (h_inj : Function.Injective (algebraMap B C))
    (n : SimplexCategoryᵒᵖ) :
    (standardToBarR B C h_inj).app n = (standardToBarROver B C n h_inj).hom.left :=
  rfl

/-- The simplicial map on naive differentials induced by `Q̄_• ⟶ R̄_•`. -/
def omegaBarQToBarRSimplicial (h_inj : Function.Injective (algebraMap B C)) :
    omegaBarQSimplicial A B C h_inj ⟶ omegaBarQSimplicial B B C h_inj where
  app n := omegaSheafMap (barQToBarROver A B C n h_inj)
  naturality n m φ := by
    have h :
        (Algebra.PolynomialTower.forgetToOverB A B C).map (tripleMap A B C φ h_inj) ≫
            barQToBarROver A B C m h_inj =
          barQToBarROver A B C n h_inj ≫
            (Algebra.PolynomialTower.forgetToOverB B B C).map (tripleMap B B C φ h_inj) := by
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      exact (barQToBarR A B C h_inj).naturality φ
    change omegaSheafMap _ ≫ omegaSheafMap _ = omegaSheafMap _ ≫ omegaSheafMap _
    rw [← omegaSheafMap_comp, ← omegaSheafMap_comp]
    exact congrArg (fun f ↦ omegaSheafMap f) h

/-- Components of `omegaBarQToBarRSimplicial` are `omegaSheafMap` of `barQToBarROver`. -/
theorem omegaBarQToBarRSimplicial_app (h_inj : Function.Injective (algebraMap B C))
    (n : SimplexCategoryᵒᵖ) :
    (omegaBarQToBarRSimplicial A B C h_inj).app n =
      omegaSheafMap (barQToBarROver A B C n h_inj) :=
  rfl

/-- The cochain map `Ω_{Q̄_•/B} ⊗ C ⟶ Ω_{R̄_•/B} ⊗ C` induced by `Q̄_• ⟶ R̄_•`. -/
def omegaBarQToBarR (h_inj : Function.Injective (algebraMap B C)) :
    omegaBarQCochain A B C h_inj ⟶ omegaBarQCochain B B C h_inj :=
  (simplicialModuleToCochain C).map (omegaBarQToBarRSimplicial A B C h_inj)

/-- `omegaBarQToBarR` is a quasi-isomorphism. -/
instance omegaBarQToBarR_quasiIso (h_inj : Function.Injective (algebraMap B C)) :
    QuasiIso (omegaBarQToBarR A B C h_inj) :=
  sorry

/-- Naive differentials `Ω_{R_•/B} ⊗_{R_•} C` of the standard resolution of `C` over `B`,
as a simplicial `C`-module. -/
abbrev omegaEvalSimplicial : SimplicialObject (ModuleCat.{u} C) :=
  asPolynomialSimplicial (standardHom B C) (standard_isPolynomial B C) ⋙ omegaSheafCov B C

/-- The cochain complex `Ω_{R_•/B} ⊗_{R_•} C` of naive differentials of the standard
resolution of `C` over `B`. -/
abbrev omegaEvalCochain : CochainComplex (ModuleCat.{u} C) ℤ :=
  (simplicialModuleToCochain C).obj (omegaEvalSimplicial B C)

/-- The simplicial map on naive differentials induced by `R_• ⟶ R̄_•`. -/
def omegaEvalToBarRSimplicial (h_inj : Function.Injective (algebraMap B C)) :
    omegaEvalSimplicial B C ⟶ omegaBarQSimplicial B B C h_inj where
  app n := omegaSheafMap (standardToBarROver B C n h_inj)
  naturality n m φ := by
    have h :
        (asPolynomialSimplicial (standardHom B C) (standard_isPolynomial B C)).map φ ≫
            standardToBarROver B C m h_inj =
          standardToBarROver B C n h_inj ≫
            (Algebra.PolynomialTower.forgetToOverB B B C).map (tripleMap B B C φ h_inj) := by
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      exact (standardToBarR B C h_inj).naturality φ
    change omegaSheafMap _ ≫ omegaSheafMap _ = omegaSheafMap _ ≫ omegaSheafMap _
    rw [← omegaSheafMap_comp, ← omegaSheafMap_comp]
    exact congrArg (fun f ↦ omegaSheafMap f) h

/-- Components of `omegaEvalToBarRSimplicial` are `omegaSheafMap` of `standardToBarROver`. -/
theorem omegaEvalToBarRSimplicial_app (h_inj : Function.Injective (algebraMap B C))
    (n : SimplexCategoryᵒᵖ) :
    (omegaEvalToBarRSimplicial B C h_inj).app n =
      omegaSheafMap (standardToBarROver B C n h_inj) :=
  rfl

/-- The cochain map `Ω_{R_•/B} ⊗ C ⟶ Ω_{R̄_•/B} ⊗ C` induced by `R_• ⟶ R̄_•`. -/
def omegaEvalToBarR (h_inj : Function.Injective (algebraMap B C)) :
    omegaEvalCochain B C ⟶ omegaBarQCochain B B C h_inj :=
  (simplicialModuleToCochain C).map (omegaEvalToBarRSimplicial B C h_inj)

/-- `omegaEvalToBarR` is a quasi-isomorphism. -/
instance omegaEvalToBarR_quasiIso (h_inj : Function.Injective (algebraMap B C)) :
    QuasiIso (omegaEvalToBarR B C h_inj) :=
  sorry

/-- Composing `omegaBarQToBarR` with the inverse of `omegaEvalToBarR` identifies
`Ω_{Q̄_•/B} ⊗_{Q̄_•} C` with `Ω_{R_•/B} ⊗_{R_•} C` in `D(C)`. -/
instance barQ_iso_omegaEval (h_inj : Function.Injective (algebraMap B C))
    [HasDerivedCategory.{q} (ModuleCat.{u} C)] :
    IsIso (DerivedCategory.Q.map (omegaBarQToBarR A B C h_inj) ≫
      inv (DerivedCategory.Q.map (omegaEvalToBarR B C h_inj))) := by
  infer_instance

end Algebra.CotangentComplex
