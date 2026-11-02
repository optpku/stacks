/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import ReasLib.Algebra.Category.ModuleCat.IdealPower.Functor
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.IdealPower
public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.Algebra.Homology.CochainComplex.FiniteProjective
public import ReasLib.LinearAlgebra.QuotientByIdeal

/-!
# Completed constant sheaves of modules

The sheaf `lim n, (M / I ^ n M)̲` attached to a module `M`, together with the
restriction-of-scalars form used for finite modules over the adic completion.
Maps, functors, cochain complexes, and termwise completed-constant models are
constructed for an arbitrary site. Geometric applications use this shared API.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Ideal.PowerQuotient
open Opposite

noncomputable section

universe u v w

namespace CategoryTheory.ConstantSheaf.AdicCompletion

variable {C : Type u} [Category.{v} C] {R : Type w} [CommRing R]

/-- The inverse system `n ↦ M / I ^ n M` in `ModuleCat R`. -/
def moduleSystem (I : Ideal R) (M : ModuleCat.{w} R) :
    ℕᵒᵖ ⥤ ModuleCat.{w} R :=
  Functor.ofOpSequence (stageStep I M)

/-- The module-level inverse system evaluates at `n` to the exact-power quotient. -/
theorem moduleSystem_obj (I : Ideal R) (M : ModuleCat.{w} R) (n : ℕ) :
    (moduleSystem I M).obj (op n) = stage I M n := rfl

/-- A module morphism induces the canonical morphism of ideal-power quotient systems. -/
def moduleSystemMap (I : Ideal R) {M N : ModuleCat.{w} R} (f : M ⟶ N) :
    moduleSystem I M ⟶ moduleSystem I N :=
  NatTrans.ofOpSequence
    (fun n ↦ ModuleCat.ofHom (f.hom.quotientMapByIdeal (I ^ n)))
    (fun n ↦ by
      simp only [moduleSystem, Functor.ofOpSequence_map_homOfLE_succ]
      ext x
      obtain ⟨x⟩ := x
      rfl)

/-- The quotient-system map preserves identities. -/
@[simp]
theorem moduleSystemMap_id (I : Ideal R) (M : ModuleCat.{w} R) :
    moduleSystemMap I (𝟙 M) = 𝟙 (moduleSystem I M) := by
  ext n x
  obtain ⟨x⟩ := x
  rfl

/-- The quotient-system map preserves composition. -/
theorem moduleSystemMap_comp (I : Ideal R) {M N P : ModuleCat.{w} R}
    (f : M ⟶ N) (g : N ⟶ P) :
    moduleSystemMap I (f ≫ g) = moduleSystemMap I f ≫ moduleSystemMap I g := by
  ext n x
  obtain ⟨x⟩ := x
  rfl

/-- The quotient-system map preserves zero morphisms. -/
@[simp]
theorem moduleSystemMap_zero (I : Ideal R) (M N : ModuleCat.{w} R) :
    moduleSystemMap I (0 : M ⟶ N) = 0 := by
  ext n x
  obtain ⟨x⟩ := x
  rfl

variable (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{w} R)]

/-- The inverse system of constant sheaves `n ↦ (M / I ^ n M)̲`. -/
def constantSystem (I : Ideal R) (M : ModuleCat.{w} R) :
    ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{w} R) :=
  moduleSystem I M ⋙ constantSheaf J (ModuleCat.{w} R)

/-- The constant-sheaf inverse system evaluates to the constant sheaf on a quotient stage. -/
theorem constantSystem_obj (I : Ideal R) (M : ModuleCat.{w} R) (n : ℕ) :
    (constantSystem J I M).obj (op n) =
      (constantSheaf J (ModuleCat.{w} R)).obj (stage I M n) := rfl

/-- The completed constant sheaf `lim n, (M / I ^ n M)` of an `R`-module. -/
def ofModule (I : Ideal R) (M : ModuleCat.{w} R) :
    Sheaf J (ModuleCat.{w} R) :=
  limit (constantSystem J I M)

/-- Projection of the completed constant sheaf onto the constant sheaf of a quotient stage. -/
def ofModule_π (I : Ideal R) (M : ModuleCat.{w} R) (n : ℕ) :
    ofModule J I M ⟶ (constantSheaf J (ModuleCat.{w} R)).obj (stage I M n) :=
  limit.π (constantSystem J I M) (op n)

/-- A module morphism induces a morphism between the completed constant sheaves. -/
def map (I : Ideal R) {M N : ModuleCat.{w} R} (f : M ⟶ N) :
    ofModule J I M ⟶ ofModule J I N :=
  lim.map (Functor.whiskerRight (moduleSystemMap I f)
    (constantSheaf J (ModuleCat.{w} R)))

/-- The map on completed constant sheaves agrees with the quotient map at every stage. -/
@[reassoc]
theorem map_π (I : Ideal R) {M N : ModuleCat.{w} R} (f : M ⟶ N) (n : ℕ) :
    map J I f ≫ ofModule_π J I N n =
      ofModule_π J I M n ≫
        (constantSheaf J (ModuleCat.{w} R)).map ((moduleSystemMap I f).app (op n)) :=
  limMap_π _ _

/-- Stagewise identification of `R / I ^ n R` with the ring quotient `R / I ^ n`. -/
def stageIsoIdealQuotient (I : Ideal R) (n : ℕ) :
    stage I (ModuleCat.of R R) n ≅ idealPowerQuotientSequence I n :=
  LinearEquiv.toModuleIso
    (Submodule.quotEquivOfEq (I ^ n • (⊤ : Submodule R R)) (I ^ n) (by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]))

/-- The inverse systems `n ↦ R / I ^ n R` and `n ↦ R / I ^ n` are isomorphic. -/
def moduleSystemIso (I : Ideal R) :
    moduleSystem I (ModuleCat.of R R) ≅ idealPowerQuotientSystem I :=
  NatIso.ofComponents (fun n ↦ stageIsoIdealQuotient I n.unop) (by
    let comparison : moduleSystem I (ModuleCat.of R R) ⟶ idealPowerQuotientSystem I :=
      NatTrans.ofOpSequence (fun n ↦ (stageIsoIdealQuotient I n).hom) (fun n ↦ by
        simp only [moduleSystem, idealPowerQuotientSystem,
          Functor.ofOpSequence_map_homOfLE_succ]
        ext x
        obtain ⟨x⟩ := x
        rfl)
    exact comparison.naturality)

/-- The constant-sheaf towers for the two quotient systems on `R` are isomorphic. -/
def constantSystemIso (I : Ideal R) :
    constantSystem J I (ModuleCat.of R R) ≅
      constantIdealPowerQuotientSheafSystem J I :=
  Functor.isoWhiskerRight (moduleSystemIso I) (constantSheaf J (ModuleCat.{w} R))

/-- The completed constant sheaf of `R` as an `R`-module agrees with the inverse limit
of the constant ideal-power quotient sheaves. -/
def ofModule_self (I : Ideal R) :
    ofModule J I (ModuleCat.of R R) ≅
      limit (constantIdealPowerQuotientSheafSystem J I) :=
  HasLimit.isoOfNatIso (constantSystemIso J I)

/-- The comparison `ofModule_self` intertwines the canonical projections to
constant quotient stages. -/
theorem ofModule_self_π (I : Ideal R) (n : ℕ) :
    (ofModule_self J I).hom ≫
        limit.π (constantIdealPowerQuotientSheafSystem J I) (op n) =
      ofModule_π J I (ModuleCat.of R R) n ≫
        (constantSheaf J (ModuleCat.{w} R)).map (stageIsoIdealQuotient I n).hom :=
  HasLimit.isoOfNatIso_hom_π (constantSystemIso J I) (op n)

/-- The completed constant sheaf of an `AdicCompletion I R`-module, regarded as
an `R`-module sheaf by restriction of scalars along `algebraMap R (AdicCompletion I R)`. -/
abbrev ofAdicModule (I : Ideal R) (M : ModuleCat.{w} (AdicCompletion I R)) :
    Sheaf J (ModuleCat.{w} R) :=
  ofModule J I ((ModuleCat.restrictScalars (algebraMap R (AdicCompletion I R))).obj M)

/-- Unfolding `ofAdicModule` recovers restriction of scalars followed by `ofModule`. -/
theorem ofAdicModule_def (I : Ideal R) (M : ModuleCat.{w} (AdicCompletion I R)) :
    ofAdicModule J I M =
      ofModule J I
        ((ModuleCat.restrictScalars (algebraMap R (AdicCompletion I R))).obj M) := rfl

/-- Restriction of scalars followed by completed constant sheaves, on objects and maps. -/
def ofAdicModuleFunctor (I : Ideal R) :
    ModuleCat.{w} (AdicCompletion I R) ⥤ Sheaf J (ModuleCat.{w} R) where
  obj M := ofAdicModule J I M
  map f := map J I ((ModuleCat.restrictScalars (algebraMap R (AdicCompletion I R))).map f)
  map_id M := by
    simp only [map, Functor.map_id, moduleSystemMap_id, Functor.whiskerRight_id']
    exact lim.map_id _
  map_comp f g := by
    simp only [map, Functor.map_comp, moduleSystemMap_comp, Functor.whiskerRight_comp]
    exact lim.map_comp _ _

/-- The functor evaluates to the existing completed constant sheaf of an adic module. -/
theorem ofAdicModuleFunctor_obj (I : Ideal R) (M : ModuleCat.{w} (AdicCompletion I R)) :
    (ofAdicModuleFunctor J I).obj M = ofAdicModule J I M := rfl

variable [Abelian (Sheaf J (ModuleCat.{w} R))]

attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory
attribute [-instance] Preadditive.fullSubcategory

/-- The completed constant sheaf functor preserves zero morphisms. -/
instance ofAdicModuleFunctor_preservesZeroMorphisms (I : Ideal R) :
    (ofAdicModuleFunctor J I).PreservesZeroMorphisms := by
  letI : (presheafToSheaf J (ModuleCat.{w} R)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  letI : (constantSheaf J (ModuleCat.{w} R)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_comp (Functor.const Cᵒᵖ) _
  refine ⟨?_⟩
  intro M N
  change map J I ((ModuleCat.restrictScalars (algebraMap R (AdicCompletion I R))).map
    (0 : M ⟶ N)) = 0
  simp only [map, Functor.map_zero, moduleSystemMap_zero, Functor.whiskerRight_zero]
  exact lim.map_zero _ _

/-- Degreewise completed constant sheaves, with differentials induced by module maps. -/
abbrev ofAdicModuleComplex (I : Ideal R) :
    CochainComplex (ModuleCat.{w} (AdicCompletion I R)) ℤ ⥤
      CochainComplex (Sheaf J (ModuleCat.{w} R)) ℤ :=
  (ofAdicModuleFunctor J I).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Evaluation of the completed constant complex in a degree. -/
theorem ofAdicModuleComplex_X (I : Ideal R)
    (M : CochainComplex (ModuleCat.{w} (AdicCompletion I R)) ℤ) (n : ℤ) :
    ((ofAdicModuleComplex J I).obj M).X n = ofAdicModule J I (M.X n) := rfl

section DerivedModels

namespace Derived

variable [HasDerivedCategory (Sheaf J (ModuleCat.{w} R))]

/-- A derived sheaf has a termwise completed-constant model when a bounded representative
has completed constant finite projective terms. Its sheaf differentials may be arbitrary. -/
def HasTermwiseCompletedConstantModel (I : Ideal R)
    (K : DerivedCategory (Sheaf J (ModuleCat.{w} R))) : Prop :=
  ∃ P : CochainComplex.Bounded (Sheaf J (ModuleCat.{w} R)),
    ∃ _ : DerivedCategory.Q.obj P.obj ≅ K,
      ∀ n : ℤ,
        ∃ M : ModuleCat.{w} (AdicCompletion I R),
          Module.Finite (AdicCompletion I R) M ∧
            Module.Projective (AdicCompletion I R) M ∧
              Nonempty (P.obj.X n ≅ ofAdicModule J I M)

/-- Unfold the termwise completed-constant model condition. -/
theorem hasTermwiseCompletedConstantModel_iff (I : Ideal R)
    (K : DerivedCategory (Sheaf J (ModuleCat.{w} R))) :
    HasTermwiseCompletedConstantModel J I K ↔
      ∃ P : CochainComplex.Bounded (Sheaf J (ModuleCat.{w} R)),
        ∃ _ : DerivedCategory.Q.obj P.obj ≅ K,
          ∀ n : ℤ,
            ∃ M : ModuleCat.{w} (AdicCompletion I R),
              Module.Finite (AdicCompletion I R) M ∧
                Module.Projective (AdicCompletion I R) M ∧
                  Nonempty (P.obj.X n ≅ ofAdicModule J I M) := Iff.rfl

/-- Termwise completed-constant models transport along derived isomorphisms. -/
theorem hasTermwiseCompletedConstantModel_of_iso (I : Ideal R)
    {K L : DerivedCategory (Sheaf J (ModuleCat.{w} R))}
    (e : K ≅ L) (h : HasTermwiseCompletedConstantModel J I K) :
    HasTermwiseCompletedConstantModel J I L := by
  obtain ⟨representative, comparison, terms⟩ := h
  exact ⟨representative, comparison ≪≫ e, terms⟩

/-- A bounded finite projective module complex gives a termwise completed-constant model. -/
theorem hasTermwiseCompletedConstantModel_of_ofAdicModuleComplex (I : Ideal R)
    (M : CochainComplex (ModuleCat.{w} (AdicCompletion I R)) ℤ)
    [M.IsBoundedFiniteProjective] :
    HasTermwiseCompletedConstantModel J I
      (DerivedCategory.Q.obj ((ofAdicModuleComplex J I).obj M)) := sorry

end Derived

end DerivedModels

end CategoryTheory.ConstantSheaf.AdicCompletion
