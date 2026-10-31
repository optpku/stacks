/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.FiniteLength.Determinant.Exact.Naturality
public import ReasLib.Algebra.Module.FiniteLength.Determinant.Exact.ThreeByThree
public import ReasLib.Algebra.Module.FiniteLength.Determinant.Exact.ExteriorPower
public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Theories of finite-length determinant lines

This file packages a functor on the core of finite-length modules together with its
short-exact comparison equivalences.  It also records the naturality, three-by-three, and
residue-field compatibility conditions used to characterize the canonical theory.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace Module.FiniteLengthDeterminant

namespace Theory

/-- The property that a bundled module has finite length. -/
def moduleProperty (R : Type u) [CommRing R] : ObjectProperty (ModuleCat.{v} R) :=
  fun M ↦ IsFiniteLength R M

/-- Membership in `moduleProperty R` is finite length of the underlying module. -/
theorem mem_moduleProperty_iff (R : Type u) [CommRing R] (M : ModuleCat.{v} R) :
    moduleProperty R M ↔ IsFiniteLength R M := Iff.rfl

/-- The property that a bundled vector space is one-dimensional. -/
def lineProperty (κ : Type u) [Field κ] : ObjectProperty (ModuleCat.{v} κ) :=
  fun L ↦ Module.finrank κ L = 1

/-- Membership in `lineProperty κ` is equality of the dimension with one. -/
theorem mem_lineProperty_iff (κ : Type u) [Field κ] (L : ModuleCat.{v} κ) :
    lineProperty κ L ↔ Module.finrank κ L = 1 := Iff.rfl

/-- The groupoid of finite-length `R`-modules and their isomorphisms. -/
abbrev ModuleCore (R : Type u) [CommRing R] :=
  Core ((moduleProperty.{u, v} R).FullSubcategory)

/-- The groupoid of one-dimensional `κ`-vector spaces and their isomorphisms. -/
abbrev LineCore (κ : Type u) [Field κ] :=
  Core ((lineProperty.{u, v} κ).FullSubcategory)

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- A finite-length bundled module regarded as an object of `ModuleCore R`. -/
def ofModule (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) : ModuleCore.{u, v} R :=
  ⟨⟨M, hM⟩⟩

/-- The underlying module of `ofModule R M hM` is `M`. -/
theorem ofModule_obj (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) :
    (ofModule R M hM).of.obj = M := rfl

/-- An isomorphism of finite-length modules as a morphism in `ModuleCore R`. -/
def ofIso {M N : ModuleCat.{v} R} (hM : IsFiniteLength R M)
    (hN : IsFiniteLength R N) (e : M ≅ N) : ofModule R M hM ⟶ ofModule R N hN :=
  ⟨ObjectProperty.isoMk (moduleProperty R) e⟩

/-- The property that a finite-length module is annihilated by the maximal ideal. -/
def residueProperty : ObjectProperty (ModuleCore.{u, v} R) :=
  fun M ↦ Module.IsTorsionBySet R M.of.obj (IsLocalRing.maximalIdeal R)

/-- Membership in `residueProperty R` means annihilation by the maximal ideal. -/
theorem mem_residueProperty_iff (M : ModuleCore.{u, v} R) :
    residueProperty R M ↔
      Module.IsTorsionBySet R M.of.obj (IsLocalRing.maximalIdeal R) := Iff.rfl

/-- The full subcategory of finite-length modules annihilated by the maximal ideal. -/
abbrev ResidueCore := (residueProperty.{u, v} R).FullSubcategory

/-- A finite-length module annihilated by the maximal ideal as an object of `ResidueCore R`. -/
def ofResidueModule (M : ModuleCat.{v} R) (hM : IsFiniteLength R M)
    (hAnn : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R)) : ResidueCore.{u, v} R :=
  ⟨ofModule R M hM, hAnn⟩

/-- The underlying bundled module of `ofResidueModule R M hM hAnn` is `M`. -/
theorem ofResidueModule_obj (M : ModuleCat.{v} R) (hM : IsFiniteLength R M)
    (hAnn : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R)) :
    (ofResidueModule R M hM hAnn).obj.of.obj = M := rfl

end Theory

/-- A determinant theory on finite-length modules: a line-valued functor together with a
comparison equivalence for every finite-length short exact sequence. -/
structure Theory (R : Type u) [CommRing R] [IsLocalRing R] where
  /-- The functor from finite-length modules and isomorphisms to residue-field lines. -/
  toFunctor : Theory.ModuleCore.{u, v} R ⥤
    Theory.LineCore.{u, max u v} (IsLocalRing.ResidueField R)
  /-- The comparison `D(K) ⊗ D(M) ≃ D(L)` attached to a short exact sequence
  `K ⟶ L ⟶ M`. -/
  comparison : ∀ (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact),
    ((toFunctor.obj (Theory.ofModule R S.X₁ h₁)).of.obj ⊗[IsLocalRing.ResidueField R]
        (toFunctor.obj (Theory.ofModule R S.X₃ h₃)).of.obj) ≃ₗ[IsLocalRing.ResidueField R]
      (toFunctor.obj (Theory.ofModule R S.X₂ h₂)).of.obj

namespace Theory

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The underlying residue-field module assigned by a determinant theory. -/
def value (D : Theory.{u, v} R) (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) :
    ModuleCat.{max u v} (IsLocalRing.ResidueField R) :=
  (D.toFunctor.obj (ofModule R M hM)).of.obj

/-- The value of a theory is the underlying object of its functor value. -/
theorem value_def (D : Theory.{u, v} R) (M : ModuleCat.{v} R)
    (hM : IsFiniteLength R M) :
    D.value M hM = (D.toFunctor.obj (ofModule R M hM)).of.obj := rfl

/-- The linear equivalence induced by a theory on an isomorphism of finite-length modules. -/
def mapEquiv (D : Theory.{u, v} R) {M N : ModuleCat.{v} R}
    (hM : IsFiniteLength R M) (hN : IsFiniteLength R N) (e : M ≅ N) :
    D.value M hM ≃ₗ[IsLocalRing.ResidueField R] D.value N hN :=
  ((lineProperty (IsLocalRing.ResidueField R)).ι.mapIso
    (D.toFunctor.map (ofIso R hM hN e)).iso).toLinearEquiv

/-- The restriction of a determinant theory to modules annihilated by the maximal ideal. -/
def restriction (D : Theory.{u, v} R) : ResidueCore.{u, v} R ⥤
    LineCore.{u, max u v} (IsLocalRing.ResidueField R) :=
  (residueProperty R).ι ⋙ D.toFunctor

/-- The object map of the residue restriction is inherited from the determinant functor. -/
theorem restriction_obj (D : Theory.{u, v} R) (M : ResidueCore.{u, v} R) :
    D.restriction.obj M = D.toFunctor.obj M.obj := rfl

/-- The morphism map of the residue restriction is inherited from the determinant functor. -/
theorem restriction_map (D : Theory.{u, v} R) {M N : ResidueCore.{u, v} R}
    (f : M ⟶ N) : D.restriction.map f = D.toFunctor.map f.hom := rfl

/-- The canonical determinant line attached to a finite-length module-core object. -/
def canonicalObj (X : ModuleCore.{u, v} R) :
    LineCore.{u, max u v} (IsLocalRing.ResidueField R) :=
  ⟨⟨ModuleCat.of (IsLocalRing.ResidueField R)
      (Module.FiniteLengthDeterminant R X.of.obj X.of.property),
    finrank_eq_one X.of.obj X.of.property⟩⟩

/-- The canonical determinant-line morphism induced by a module-core morphism. -/
def canonicalMap (R : Type u) [CommRing R] [IsLocalRing R]
    {X Y : ModuleCore.{u, v} R} (f : X ⟶ Y) :
    canonicalObj X ⟶ canonicalObj Y :=
  ⟨ObjectProperty.isoMk (lineProperty (IsLocalRing.ResidueField R))
    (Module.FiniteLengthDeterminant.mapEquiv X.of.property Y.of.property
      ((moduleProperty R).ι.mapIso f.iso).toLinearEquiv).toModuleIso⟩

/-- The canonical determinant-line map preserves identity morphisms. -/
theorem canonicalMap_id (X : ModuleCore.{u, v} R) :
    canonicalMap R (𝟙 X) = 𝟙 (canonicalObj X) := by
  apply Core.hom_ext
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  exact congrArg LinearEquiv.toLinearMap
    (Module.FiniteLengthDeterminant.mapEquiv_refl X.of.property)

/-- The canonical determinant-line map preserves composition. -/
theorem canonicalMap_comp {X Y Z : ModuleCore.{u, v} R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    canonicalMap R (f ≫ g) = canonicalMap R f ≫ canonicalMap R g := by
  apply Core.hom_ext
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  exact congrArg LinearEquiv.toLinearMap
    (Module.FiniteLengthDeterminant.mapEquiv_trans X.of.property Y.of.property Z.of.property
      ((moduleProperty R).ι.mapIso f.iso).toLinearEquiv
      ((moduleProperty R).ι.mapIso g.iso).toLinearEquiv).symm

/-- The concrete determinant functor on finite-length modules and isomorphisms. -/
def canonicalFunctor : ModuleCore.{u, v} R ⥤
    LineCore.{u, max u v} (IsLocalRing.ResidueField R) where
  obj := canonicalObj
  map := canonicalMap R
  map_id := canonicalMap_id
  map_comp := canonicalMap_comp

/-- The canonical functor sends an object to its explicitly bundled determinant line. -/
theorem canonicalFunctor_obj (X : ModuleCore.{u, v} R) :
    canonicalFunctor.obj X = canonicalObj X := rfl

/-- The canonical functor sends a core morphism to determinant-symbol transport. -/
theorem canonicalFunctor_map {X Y : ModuleCore.{u, v} R} (f : X ⟶ Y) :
    canonicalFunctor.map f = canonicalMap R f := rfl

/-- The canonical determinant theory built from determinant symbols and short-exact
concatenation. -/
def canonical (R : Type u) [CommRing R] [IsLocalRing R] : Theory.{u, v} R where
  toFunctor := canonicalFunctor
  comparison := fun S h₁ h₂ h₃ hS ↦ exactEquiv S h₁ h₂ h₃ hS

/-- The functor field of the canonical theory is `canonicalFunctor`. -/
theorem canonical_toFunctor : (canonical R).toFunctor = canonicalFunctor := rfl

/-- The comparison field of the canonical theory is the concrete `exactEquiv`. -/
theorem canonical_comparison (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact) :
    (canonical R).comparison S h₁ h₂ h₃ hS = exactEquiv S h₁ h₂ h₃ hS := rfl

/-- The row-first comparison map of a determinant theory on a three-by-three diagram. -/
def viaRows (D : Theory.{u, v} R) (T : ThreeByThree.{u, v} R) :
    ((D.value T.top.X₁ T.topFiniteLeft ⊗[IsLocalRing.ResidueField R]
          D.value T.top.X₃ T.topFiniteRight) ⊗[IsLocalRing.ResidueField R]
        (D.value T.bottom.X₁ T.bottomFiniteLeft ⊗[IsLocalRing.ResidueField R]
          D.value T.bottom.X₃ T.bottomFiniteRight)) →ₗ[IsLocalRing.ResidueField R]
      D.value T.middle.X₂ T.middleFiniteMiddle :=
  (D.comparison (ThreeByThree.columnMiddle T) T.topFiniteMiddle T.middleFiniteMiddle
      T.bottomFiniteMiddle T.centerExact).toLinearMap.comp
    (TensorProduct.congr
      (D.comparison T.top T.topFiniteLeft T.topFiniteMiddle T.topFiniteRight T.topExact)
      (D.comparison T.bottom T.bottomFiniteLeft T.bottomFiniteMiddle
        T.bottomFiniteRight T.bottomExact)).toLinearMap

/-- The column-first comparison map, including the Koszul interchange sign. -/
def viaColumns (D : Theory.{u, v} R) (T : ThreeByThree.{u, v} R) :
    ((D.value T.top.X₁ T.topFiniteLeft ⊗[IsLocalRing.ResidueField R]
          D.value T.top.X₃ T.topFiniteRight) ⊗[IsLocalRing.ResidueField R]
        (D.value T.bottom.X₁ T.bottomFiniteLeft ⊗[IsLocalRing.ResidueField R]
          D.value T.bottom.X₃ T.bottomFiniteRight)) →ₗ[IsLocalRing.ResidueField R]
      D.value T.middle.X₂ T.middleFiniteMiddle :=
  (D.comparison T.middle T.middleFiniteLeft T.middleFiniteMiddle
      T.middleFiniteRight T.middleExact).toLinearMap.comp
    ((TensorProduct.congr
      (D.comparison (ThreeByThree.columnLeft T) T.topFiniteLeft T.middleFiniteLeft
        T.bottomFiniteLeft T.leftExact)
      (D.comparison (ThreeByThree.columnRight T) T.topFiniteRight T.middleFiniteRight
        T.bottomFiniteRight T.rightExact)).toLinearMap.comp
      (ModuleCat.TensorProduct.koszulShuffle (IsLocalRing.ResidueField R)
        (D.value T.top.X₁ T.topFiniteLeft) (D.value T.top.X₃ T.topFiniteRight)
        (D.value T.bottom.X₁ T.bottomFiniteLeft)
        (D.value T.bottom.X₃ T.bottomFiniteRight)
        (length R T.top.X₃ T.topFiniteRight : ℤ)
        (length R T.bottom.X₁ T.bottomFiniteLeft : ℤ)).hom)

/-- Naturality of the short-exact comparison maps under isomorphisms of short complexes. -/
def IsNatural (D : Theory.{u, v} R) : Prop :=
  ∀ (S T : ShortComplex (ModuleCat.{v} R))
    (hS₁ : IsFiniteLength R S.X₁) (hS₂ : IsFiniteLength R S.X₂)
    (hS₃ : IsFiniteLength R S.X₃) (hT₁ : IsFiniteLength R T.X₁)
    (hT₂ : IsFiniteLength R T.X₂) (hT₃ : IsFiniteLength R T.X₃)
    (hS : S.ShortExact) (e : S ≅ T),
    (D.comparison T hT₁ hT₂ hT₃ (ShortComplex.shortExact_of_iso e hS)).toLinearMap.comp
        (TensorProduct.congr
          (D.mapEquiv hS₁ hT₁ (ShortComplex.π₁.mapIso e))
          (D.mapEquiv hS₃ hT₃ (ShortComplex.π₃.mapIso e))).toLinearMap =
      (D.mapEquiv hS₂ hT₂ (ShortComplex.π₂.mapIso e)).toLinearMap.comp
        (D.comparison S hS₁ hS₂ hS₃ hS).toLinearMap

/-- The naturality predicate unfolded as its commuting comparison equation. -/
theorem isNatural_iff (D : Theory.{u, v} R) : D.IsNatural ↔
    ∀ (S T : ShortComplex (ModuleCat.{v} R))
      (hS₁ : IsFiniteLength R S.X₁) (hS₂ : IsFiniteLength R S.X₂)
      (hS₃ : IsFiniteLength R S.X₃) (hT₁ : IsFiniteLength R T.X₁)
      (hT₂ : IsFiniteLength R T.X₂) (hT₃ : IsFiniteLength R T.X₃)
      (hS : S.ShortExact) (e : S ≅ T),
      (D.comparison T hT₁ hT₂ hT₃ (ShortComplex.shortExact_of_iso e hS)).toLinearMap.comp
          (TensorProduct.congr
            (D.mapEquiv hS₁ hT₁ (ShortComplex.π₁.mapIso e))
            (D.mapEquiv hS₃ hT₃ (ShortComplex.π₃.mapIso e))).toLinearMap =
        (D.mapEquiv hS₂ hT₂ (ShortComplex.π₂.mapIso e)).toLinearMap.comp
          (D.comparison S hS₁ hS₂ hS₃ hS).toLinearMap := Iff.rfl

/-- Signed three-by-three coherence for a determinant theory. -/
def IsCoherent (D : Theory.{u, v} R) : Prop :=
  ∀ T : ThreeByThree.{u, v} R, viaRows D T = viaColumns D T

/-- The coherence predicate unfolded as equality of its two named routes. -/
theorem isCoherent_iff (D : Theory.{u, v} R) :
    D.IsCoherent ↔ ∀ T : ThreeByThree.{u, v} R, viaRows D T = viaColumns D T := Iff.rfl

/-- The linear equivalence underlying a component of an isomorphism of determinant
functors. -/
def functorEquiv {D E : Theory.{u, v} R} (e : D.toFunctor ≅ E.toFunctor)
    (X : ModuleCore.{u, v} R) :
    (D.toFunctor.obj X).of.obj ≃ₗ[IsLocalRing.ResidueField R]
      (E.toFunctor.obj X).of.obj :=
  ((lineProperty (IsLocalRing.ResidueField R)).ι.mapIso (e.app X).hom.iso).toLinearEquiv

/-- The linear equivalence underlying a component of a residue normalization. -/
def normalizationEquiv {D E : Theory.{u, v} R} (e : D.restriction ≅ E.restriction)
    (X : ResidueCore.{u, v} R) :
    (D.restriction.obj X).of.obj ≃ₗ[IsLocalRing.ResidueField R]
      (E.restriction.obj X).of.obj :=
  ((lineProperty (IsLocalRing.ResidueField R)).ι.mapIso (e.app X).hom.iso).toLinearEquiv

/-- Compatibility of a residue normalization with the comparison for one short exact
sequence annihilated by the maximal ideal. -/
def ResidueCompatibleAt (D : Theory.{u, v} R)
    (e : D.restriction ≅ (canonical R).restriction)
    (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact)
    (hAnn₁ : Module.IsTorsionBySet R S.X₁ (IsLocalRing.maximalIdeal R))
    (hAnn₂ : Module.IsTorsionBySet R S.X₂ (IsLocalRing.maximalIdeal R))
    (hAnn₃ : Module.IsTorsionBySet R S.X₃ (IsLocalRing.maximalIdeal R)) : Prop :=
  ((canonical R).comparison S h₁ h₂ h₃ hS).toLinearMap.comp
      (TensorProduct.congr
        (normalizationEquiv e (ofResidueModule R S.X₁ h₁ hAnn₁))
        (normalizationEquiv e (ofResidueModule R S.X₃ h₃ hAnn₃))).toLinearMap =
    (normalizationEquiv e (ofResidueModule R S.X₂ h₂ hAnn₂)).toLinearMap.comp
      (D.comparison S h₁ h₂ h₃ hS).toLinearMap

/-- Agreement of a residue normalization with all short-exact comparison equivalences. -/
def AgreesOnResidue (D : Theory.{u, v} R)
    (e : D.restriction ≅ (canonical R).restriction) : Prop :=
  ∀ (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact)
    (hAnn₁ : Module.IsTorsionBySet R S.X₁ (IsLocalRing.maximalIdeal R))
    (hAnn₂ : Module.IsTorsionBySet R S.X₂ (IsLocalRing.maximalIdeal R))
    (hAnn₃ : Module.IsTorsionBySet R S.X₃ (IsLocalRing.maximalIdeal R)),
    ResidueCompatibleAt D e S h₁ h₂ h₃ hS hAnn₁ hAnn₂ hAnn₃

/-- The residue-agreement predicate unfolded as its comparison square. -/
theorem agreesOnResidue_iff (D : Theory.{u, v} R)
    (e : D.restriction ≅ (canonical R).restriction) :
    D.AgreesOnResidue e ↔
      ∀ (S : ShortComplex (ModuleCat.{v} R))
        (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
        (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact)
        (hAnn₁ : Module.IsTorsionBySet R S.X₁ (IsLocalRing.maximalIdeal R))
        (hAnn₂ : Module.IsTorsionBySet R S.X₂ (IsLocalRing.maximalIdeal R))
        (hAnn₃ : Module.IsTorsionBySet R S.X₃ (IsLocalRing.maximalIdeal R)),
        ResidueCompatibleAt D e S h₁ h₂ h₃ hS hAnn₁ hAnn₂ hAnn₃ := Iff.rfl

/-- Compatibility of a functor isomorphism with every short-exact comparison equivalence. -/
def Compatible (D E : Theory.{u, v} R) (e : D.toFunctor ≅ E.toFunctor) : Prop :=
  ∀ (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact),
    (E.comparison S h₁ h₂ h₃ hS).toLinearMap.comp
        (TensorProduct.congr
          (functorEquiv e (ofModule R S.X₁ h₁))
          (functorEquiv e (ofModule R S.X₃ h₃))).toLinearMap =
      (functorEquiv e (ofModule R S.X₂ h₂)).toLinearMap.comp
        (D.comparison S h₁ h₂ h₃ hS).toLinearMap

/-- An isomorphism of determinant theories, including compatibility with the short-exact
comparison equivalences. -/
structure Iso (D E : Theory.{u, v} R) where
  /-- The natural isomorphism of the underlying line-valued functors. -/
  functorIso : D.toFunctor ≅ E.toFunctor
  /-- Compatibility of `functorIso` with every short-exact comparison equivalence. -/
  comparison_comm : Compatible D E functorIso

namespace Iso

/-- The identity functor isomorphism is compatible with the comparison equivalences. -/
theorem refl_compatible (D : Theory.{u, v} R) :
    Compatible D D (CategoryTheory.Iso.refl D.toFunctor) := by
  intro S h₁ h₂ h₃ hS
  have hid (X : ModuleCore.{u, v} R) :
      functorEquiv (CategoryTheory.Iso.refl D.toFunctor) X =
        LinearEquiv.refl (IsLocalRing.ResidueField R) _ := by
    ext x
    rfl
  simp only [hid, TensorProduct.congr_refl_refl, LinearEquiv.refl_toLinearMap,
    LinearMap.comp_id, LinearMap.id_comp]

/-- The identity isomorphism of a determinant theory. -/
def refl (D : Theory.{u, v} R) : Iso D D where
  functorIso := CategoryTheory.Iso.refl D.toFunctor
  comparison_comm := refl_compatible D

/-- The inverse of a compatible functor isomorphism is compatible. -/
theorem symm_compatible {D E : Theory.{u, v} R} (e : Iso D E) :
    Compatible E D e.functorIso.symm := by
  have hcancel (X : ModuleCore.{u, v} R) (x : (E.toFunctor.obj X).of.obj) :
      functorEquiv e.functorIso X (functorEquiv e.functorIso.symm X x) = x := by
    exact congrArg (fun f : E.toFunctor.obj X ⟶ E.toFunctor.obj X =>
      f.iso.hom.hom.hom x) (e.functorIso.inv_hom_id_app X)
  have hcancel' (X : ModuleCore.{u, v} R) (x : (D.toFunctor.obj X).of.obj) :
      functorEquiv e.functorIso.symm X (functorEquiv e.functorIso X x) = x := by
    exact congrArg (fun f : D.toFunctor.obj X ⟶ D.toFunctor.obj X =>
      f.iso.hom.hom.hom x) (e.functorIso.hom_inv_id_app X)
  intro S h₁ h₂ h₃ hS
  apply TensorProduct.ext'
  intro x y
  have h := congrArg (fun z => functorEquiv e.functorIso.symm (ofModule R S.X₂ h₂) z)
    (LinearMap.congr_fun (e.comparison_comm S h₁ h₂ h₃ hS)
      (functorEquiv e.functorIso.symm (ofModule R S.X₁ h₁) x ⊗ₜ[IsLocalRing.ResidueField R]
        functorEquiv e.functorIso.symm (ofModule R S.X₃ h₃) y))
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.congr_tmul,
    hcancel, hcancel'] using h.symm

/-- The inverse of an isomorphism of determinant theories. -/
def symm {D E : Theory.{u, v} R} (e : Iso D E) : Iso E D where
  functorIso := e.functorIso.symm
  comparison_comm := symm_compatible e

/-- A composite of compatible functor isomorphisms is compatible. -/
theorem trans_compatible {D E F : Theory.{u, v} R} (e : Iso D E) (f : Iso E F) :
    Compatible D F (e.functorIso ≪≫ f.functorIso) := by
  have hcomp (X : ModuleCore.{u, v} R) :
      functorEquiv (e.functorIso ≪≫ f.functorIso) X =
        (functorEquiv e.functorIso X).trans (functorEquiv f.functorIso X) := by
    ext x
    rfl
  intro S h₁ h₂ h₃ hS
  simp only [hcomp, TensorProduct.congr_trans, LinearEquiv.coe_trans, LinearMap.comp_assoc]
  rw [← LinearMap.comp_assoc, f.comparison_comm S h₁ h₂ h₃ hS,
    LinearMap.comp_assoc, e.comparison_comm S h₁ h₂ h₃ hS]

/-- The composite of two isomorphisms of determinant theories. -/
def trans {D E F : Theory.{u, v} R} (e : Iso D E) (f : Iso E F) : Iso D F where
  functorIso := e.functorIso ≪≫ f.functorIso
  comparison_comm := trans_compatible e f

/-- Restrict an isomorphism of determinant theories to maximal-ideal-annihilated modules. -/
def restrict {D E : Theory.{u, v} R} (e : Iso D E) : D.restriction ≅ E.restriction :=
  Functor.isoWhiskerLeft (residueProperty R).ι e.functorIso

/-- The component of a restricted theory isomorphism is its original component. -/
theorem restrict_app {D E : Theory.{u, v} R} (e : Iso D E)
    (X : ResidueCore.{u, v} R) :
    (e.restrict.app X).hom.iso = (e.functorIso.app X.obj).hom.iso := rfl

end Iso

/-- The canonical determinant theory satisfies naturality. -/
theorem canonical_isNatural : (canonical R).IsNatural := by
  intro S T hS₁ hS₂ hS₃ hT₁ hT₂ hT₃ hS e
  exact exactEquiv_naturality hS₁ hS₂ hS₃ hT₁ hT₂ hT₃ hS e

/-- The canonical determinant theory satisfies signed three-by-three coherence. -/
theorem canonical_isCoherent : (canonical R).IsCoherent := by
  intro T
  exact ThreeByThree.commutes T

/-- The canonical determinant theory agrees with itself on the residue subcategory. -/
theorem canonical_agreesOnResidue :
    (canonical R).AgreesOnResidue
      (CategoryTheory.Iso.refl (canonical R).restriction) := by
  intro S h₁ h₂ h₃ hS hAnn₁ hAnn₂ hAnn₃
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rfl

end Theory

end Module.FiniteLengthDeterminant
