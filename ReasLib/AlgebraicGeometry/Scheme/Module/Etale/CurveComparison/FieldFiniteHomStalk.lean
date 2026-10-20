/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FieldLocalHomStalk
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FieldExactTransport
public import ReasLib.Algebra.Homology.HomologicalComplex.PreservesHomology
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Homology.QuasiIso

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace FieldFiniteHomStalk
variable (k : Type u) [Field k]

/-- The actual module-valued geometric stalk; it does not take Galois invariants. -/
def stalk (R : Type (u + 1)) [Ring R] :
    Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u + 1} R) ⥤ ModuleCat.{u + 1} R :=
  (FieldModuleDescent.point k).sheafFiber

instance stalk_additive (R : Type (u + 1)) [Ring R] : (stalk k R).Additive := by sorry
instance stalk_preservesHomology (R : Type (u + 1)) [Ring R] : (stalk k R).PreservesHomology := by sorry
instance stalk_reflectsIsomorphisms (R : Type (u + 1)) [Ring R] : (stalk k R).ReflectsIsomorphisms := by sorry

def stalkAb (R : Type (u + 1)) [Ring R] := stalk k R ⋙ forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
instance stalkAb_additive (R : Type (u + 1)) [Ring R] : (stalkAb k R).Additive := by
  unfold stalkAb
  infer_instance
instance stalkAb_preservesHomology (R : Type (u + 1)) [Ring R] : (stalkAb k R).PreservesHomology := by sorry
instance stalkAb_reflectsIsomorphisms (R : Type (u + 1)) [Ring R] : (stalkAb k R).ReflectsIsomorphisms := by sorry

def underlyingRepresentation (R : Type (u + 1)) [Ring R] :
    DiscreteModuleCat R Gal(AlgebraicClosure k/k) ⥤ ModuleCat.{u + 1} R where
  obj M := M.obj.V
  map f := f.hom.hom
  map_id := by intros; rfl
  map_comp := by intros; rfl

def inverseStalkIso (R : Type (u + 1)) [Ring R]
    (M : DiscreteModuleCat R Gal(AlgebraicClosure k/k)) :
    (stalk k R).obj ((FieldModuleDescent.inverse k R).obj M) ≅ M.obj.V :=
  (underlyingRepresentation k R).mapIso ((FieldModuleDescent.equivalence k R).counitIso.app M)

theorem inverse_stalk_finite (R : Type (u + 1)) [Ring R]
    (M : DiscreteModuleCat R Gal(AlgebraicClosure k/k)) [Finite M.obj.V] :
    Finite ((stalk k R).obj ((FieldModuleDescent.inverse k R).obj M)) :=
  Finite.of_equiv M.obj.V (inverseStalkIso k R M).symm.toLinearEquiv.toEquiv

variable {A R : Type (u + 1)} [CommRing A] [Ring R]
variable (h : A →+* R) (hc : ∀ (a : A) (r : R), h a * r = r * h a)
variable [(Spec (CommRingCat.of k)).smallEtaleTopology.HasSheafCompose (NoncommLocalHom.modules h)]
variable [(Spec (CommRingCat.of k)).smallEtaleTopology.HasSheafCompose
  (ModuleCat.restrictScalars (NoncommLocalHom.opScalarHom h hc))]
variable (F : Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u + 1} R))

/-- The actual local-Hom functor in its second argument. -/
def localHom : Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
    Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ) where
  obj J := NoncommLocalHom.obj h hc (Spec (CommRingCat.of k)) F J
  map f := NoncommLocalHom.postcomp h hc (Spec (CommRingCat.of k)) f
  map_id := by sorry
  map_comp := by sorry

instance localHom_additive : (localHom k h hc F).Additive := by sorry

abbrev sourceModule := (NoncommLocalHom.modules h).obj ((FieldModuleDescent.forward k R).obj F).obj.V

/-- Ordinary A-linear Hom of stalk modules. This is not Hom in the Galois category. -/
def moduleHom : ModuleCat.{u + 1} A ⥤ AddCommGrpCat.{u + 1} :=
  preadditiveCoyoneda.obj (op (sourceModule k h F))

instance moduleHom_additive : (moduleHom k h F).Additive := by
  unfold moduleHom
  infer_instance

def evaluate (J : Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (stalkAb k Rᵐᵒᵖ).obj ((localHom k h hc F).obj J) ⟶
    (moduleHom k h F).obj ((stalk k A).obj J) :=
  AddCommGrpCat.ofHom
    { toFun := fun α ↦ ConcreteCategory.ofHom (C := ModuleCat.{u + 1} A)
        (FieldLocalHomStalk.evaluate k h hc F J α)
      map_zero' := by sorry
      map_add' := by sorry }

variable [hF : Finite ((stalk k R).obj F)]
include hF in
/-- Finite field stalks give finite locally constant sheaves. Finite presentation
over finite A is sufficient for this comparison; projectivity is not used. -/
theorem evaluate_bijective [Finite A]
    (J : Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u + 1} A)) :
    Function.Bijective (evaluate k h hc F J).hom := by sorry

/-- Canonical germ evaluation, natural in the target sheaf, with its actual inverse. -/
def iso [Finite A] : localHom k h hc F ⋙ stalkAb k Rᵐᵒᵖ ≅ stalk k A ⋙ moduleHom k h F :=
  NatIso.ofComponents (fun J ↦ (AddEquiv.ofBijective (evaluate k h hc F J).hom
    (evaluate_bijective k h hc F J)).toAddCommGrpIso) (by sorry)

/-- The finite-Hom/stalk comparison on actual cochain complexes. -/
def cochainIso [Finite A] :
    (localHom k h hc F).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      (stalkAb k Rᵐᵒᵖ).mapHomologicalComplex (ComplexShape.up ℕ) ≅
    (stalk k A).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      (moduleHom k h F).mapHomologicalComplex (ComplexShape.up ℕ) :=
  Functor.mapHomologicalComplexCompIso (Iso.refl (localHom k h hc F ⋙ stalkAb k Rᵐᵒᵖ)) _ ≪≫
    NatIso.mapHomologicalComplex (iso k h hc F) _ ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (stalk k A ⋙ moduleHom k h F)) _).symm

theorem quasiIso_iff [Finite A]
    {J K : CochainComplex (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u + 1} A)) ℕ}
    (g : J ⟶ K) :
    QuasiIso (((stalkAb k Rᵐᵒᵖ).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (((localHom k h hc F).mapHomologicalComplex (ComplexShape.up ℕ)).map g)) ↔
    QuasiIso (((moduleHom k h F).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (((stalk k A).mapHomologicalComplex (ComplexShape.up ℕ)).map g)) :=
  quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk ((cochainIso k h hc F).app J) ((cochainIso k h hc F).app K)
      ((cochainIso k h hc F).hom.naturality g).symm)

end FieldFiniteHomStalk
