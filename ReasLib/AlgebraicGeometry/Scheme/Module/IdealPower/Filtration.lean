/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Product
public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.Homology

/-!
# Ideal-power filtrations of complexes of scheme modules

This module packages the powers of quasi-coherent ideal-sheaf data as a functorial
decreasing filtration and applies it degreewise to cochain complexes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

namespace IdealPowerFiltration

/-- The ideal-power subobjects of a scheme module form an antitone family indexed by `ℤ`. -/
theorem antitone (I : X.IdealSheafData) (M : X.Modules) :
    Antitone (fun q : ℤ ↦ idealPowerProductSubobject I M q.toNat) := sorry

/-- The ideal-power subobjects, viewed monotonically on the order dual of `ℤ`. -/
theorem monotone (I : X.IdealSheafData) (M : X.Modules) :
    Monotone (fun q : ℤᵒᵈ ↦
      idealPowerProductSubobject I M (OrderDual.ofDual q).toNat) :=
  fun _ _ h ↦ antitone I M h

/-- The decreasing ideal-power filtration of a scheme module. -/
noncomputable def filtration (I : X.IdealSheafData) (M : X.Modules) :
    DecreasingFiltration M where
  toFun q := idealPowerProductSubobject I M (OrderDual.ofDual q).toNat
  monotone' := monotone I M

/-- A natural-number stage of the ideal-power filtration is the corresponding ideal-power
subobject. -/
theorem filtration_stage_nat (I : X.IdealSheafData) (M : X.Modules) (n : ℕ) :
    (filtration I M).stage (n : ℤ) = idealPowerProductSubobject I M n := rfl

open CategoryTheory.MonoidalCategory in
private theorem idealPowerAction_naturality
    {C : Type*} [Category C] [MonoidalCategory C] {U T A B : C}
    (j : T ⟶ U) (e : U ≅ 𝟙_ C) (t : A ⟶ B) :
    T ◁ t ≫ j ▷ B ≫ e.hom ▷ B ≫ (λ_ B).hom =
      (j ▷ A ≫ e.hom ▷ A ≫ (λ_ A).hom) ≫ t := by
  simp only [Category.assoc, whisker_exchange_assoc, leftUnitor_naturality]

open CategoryTheory.MonoidalCategory in
/-- Every morphism of scheme modules preserves all ideal-power filtration stages. -/
theorem map_factors (I : X.IdealSheafData) {M N : X.Modules} (f : M ⟶ N) (q : ℤ) :
    (idealPowerProductSubobject I N q.toNat).Factors
      ((idealPowerProductSubobject I M q.toNat).arrow ≫ f) := by
  let J := (I ^ q.toNat).toSubobject
  let T : X.Modules := Subobject.underlying.obj J
  let A : X.Modules := Subobject.underlying.obj (⊤ : Subobject M)
  let B : X.Modules := Subobject.underlying.obj (⊤ : Subobject N)
  let t : A ⟶ B :=
    (⊤ : Subobject M).arrow ≫ f ≫ inv (⊤ : Subobject N).arrow
  have ht : t ≫ (⊤ : Subobject N).arrow = (⊤ : Subobject M).arrow ≫ f := by
    simp only [t, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hn :
      T ◁ t ≫ SheafOfModules.RingedSite.IdealSheaf.action J B =
        SheafOfModules.RingedSite.IdealSheaf.action J A ≫ t := by
    exact idealPowerAction_naturality (C := X.Modules) J.arrow
      (SheafOfModules.RingedSite.unitIsoTensorUnit
        (J := Opens.grothendieckTopology X.toTopCat) (𝒪 := X.𝒪)) t
  let a : tensorObj T A ⟶ M :=
    SheafOfModules.RingedSite.IdealSheaf.action J A ≫ (⊤ : Subobject M).arrow
  let b : tensorObj T B ⟶ N :=
    SheafOfModules.RingedSite.IdealSheaf.action J B ≫ (⊤ : Subobject N).arrow
  let sq : Arrow.mk a ⟶ Arrow.mk b :=
    Arrow.homMk (T ◁ t) f (by
      change (T ◁ t) ≫
          (SheafOfModules.RingedSite.IdealSheaf.action J B ≫
            (⊤ : Subobject N).arrow) =
        (SheafOfModules.RingedSite.IdealSheaf.action J A ≫
          (⊤ : Subobject M).arrow) ≫ f
      calc
        _ = ((T ◁ t) ≫ SheafOfModules.RingedSite.IdealSheaf.action J B) ≫
            (⊤ : Subobject N).arrow := (Category.assoc _ _ _).symm
        _ = (SheafOfModules.RingedSite.IdealSheaf.action J A ≫ t) ≫
            (⊤ : Subobject N).arrow := congrArg (fun k ↦ k ≫ (⊤ : Subobject N).arrow) hn
        _ = SheafOfModules.RingedSite.IdealSheaf.action J A ≫
            (t ≫ (⊤ : Subobject N).arrow) := Category.assoc _ _ _
        _ = SheafOfModules.RingedSite.IdealSheaf.action J A ≫
            ((⊤ : Subobject M).arrow ≫ f) :=
          congrArg (fun k ↦ SheafOfModules.RingedSite.IdealSheaf.action J A ≫ k) ht
        _ = _ := (Category.assoc _ _ _).symm)
  change (imageSubobject b).Factors ((imageSubobject a).arrow ≫ f)
  exact (Subobject.factors_iff _ _).mpr
    ⟨imageSubobjectMap sq, imageSubobjectMap_arrow sq⟩

/-- Every morphism of scheme modules preserves the bundled ideal-power filtrations. -/
theorem map_preserves (I : X.IdealSheafData) {M N : X.Modules} (f : M ⟶ N) (q : ℤ) :
    ((filtration I N).stage q).Factors (((filtration I M).stage q).arrow ≫ f) :=
  map_factors I f q

/-- The functor sending a scheme module to its ideal-power filtered object. -/
noncomputable def filtered (I : X.IdealSheafData) :
    X.Modules ⥤ FilteredObject X.Modules where
  obj M :=
    { obj := M
      filtration := filtration I M }
  map f :=
    { hom := f
      preserves := map_preserves I f }
  map_id _ := FilteredObject.Hom.ext rfl
  map_comp _ _ := FilteredObject.Hom.ext rfl

/-- The ideal-power filtration functor preserves zero morphisms. -/
instance filtered_preservesZeroMorphisms (I : X.IdealSheafData) :
    (filtered I).PreservesZeroMorphisms where
  map_zero _ _ := FilteredObject.Hom.ext rfl

/-- The underlying object of the ideal-power filtered module is the original module. -/
theorem filtered_obj (I : X.IdealSheafData) (M : X.Modules) :
    ((filtered I).obj M).obj = M := rfl

/-- The underlying morphism of the ideal-power filtered map is the original morphism. -/
theorem filtered_map_hom (I : X.IdealSheafData) {M N : X.Modules} (f : M ⟶ N) :
    ((filtered I).map f).hom = f := rfl

end IdealPowerFiltration

namespace IdealPowerComplex

/-- A cochain complex with the ideal-power filtration placed on every term. -/
noncomputable def filtered (I : X.IdealSheafData) (K : CochainComplex X.Modules ℤ) :
    CochainComplex (FilteredObject X.Modules) ℤ :=
  ((IdealPowerFiltration.filtered I).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- Forgetting the ideal-power filtration canonically recovers the original complex. -/
noncomputable def underlyingIso (I : X.IdealSheafData) (K : CochainComplex X.Modules ℤ) :
    HomologicalComplex.Filtered.underlying (filtered I K) ≅ K where
  hom :=
    { f := fun _ ↦ 𝟙 _
      comm' := by
        intro i j _
        change K.d i j ≫ 𝟙 _ = 𝟙 _ ≫ K.d i j
        simp only [Category.comp_id, Category.id_comp] }
  inv :=
    { f := fun _ ↦ 𝟙 _
      comm' := by
        intro i j _
        change K.d i j ≫ 𝟙 _ = 𝟙 _ ≫ K.d i j
        simp only [Category.comp_id, Category.id_comp] }
  hom_inv_id := by
    apply HomologicalComplex.hom_ext
    intro i
    change (𝟙 (K.X i)) ≫ 𝟙 (K.X i) = 𝟙 (K.X i)
    exact Category.id_comp _
  inv_hom_id := by
    apply HomologicalComplex.hom_ext
    intro i
    change (𝟙 (K.X i)) ≫ 𝟙 (K.X i) = 𝟙 (K.X i)
    exact Category.id_comp _

/-- The forward map of `underlyingIso` is degreewise the identity. -/
theorem underlyingIso_hom_f (I : X.IdealSheafData) (K : CochainComplex X.Modules ℤ)
    (i : ℤ) :
    (underlyingIso I K).hom.f i = 𝟙 (K.X i) := rfl

/-- The term in degree `i` of the natural-number stage `n` is the object underlying
`I ^ n K.X i`. -/
theorem stage_X (I : X.IdealSheafData) (K : CochainComplex X.Modules ℤ)
    (n : ℕ) (i : ℤ) :
    (HomologicalComplex.Filtered.Stage.complex (filtered I K) (n : ℤ)).X i =
      (idealPowerProductSubobject I (K.X i) n : X.Modules) := rfl

/-- The map from a natural-number filtration stage to the underlying complex is the termwise
ideal-power inclusion. -/
theorem stage_inclusion_f (I : X.IdealSheafData) (K : CochainComplex X.Modules ℤ)
    (n : ℕ) (i : ℤ) :
    (HomologicalComplex.Filtered.Stage.inclusion (filtered I K) (n : ℤ)).f i =
      (((filtered I K).X i).filtration.stage (n : ℤ)).arrow := rfl

end IdealPowerComplex

end AlgebraicGeometry.Scheme.Modules
