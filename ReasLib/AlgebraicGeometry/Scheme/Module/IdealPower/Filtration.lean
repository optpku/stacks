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
      idealPowerProductSubobject I M (OrderDual.ofDual q).toNat) := sorry

/-- The decreasing ideal-power filtration of a scheme module. -/
noncomputable def filtration (I : X.IdealSheafData) (M : X.Modules) :
    DecreasingFiltration M where
  toFun q := idealPowerProductSubobject I M (OrderDual.ofDual q).toNat
  monotone' := monotone I M

/-- A natural-number stage of the ideal-power filtration is the corresponding ideal-power
subobject. -/
theorem filtration_stage_nat (I : X.IdealSheafData) (M : X.Modules) (n : ℕ) :
    (filtration I M).stage (n : ℤ) = idealPowerProductSubobject I M n := sorry

/-- Every morphism of scheme modules preserves all ideal-power filtration stages. -/
theorem map_factors (I : X.IdealSheafData) {M N : X.Modules} (f : M ⟶ N) (q : ℤ) :
    (idealPowerProductSubobject I N q.toNat).Factors
      ((idealPowerProductSubobject I M q.toNat).arrow ≫ f) := sorry

/-- Every morphism of scheme modules preserves the bundled ideal-power filtrations. -/
theorem map_preserves (I : X.IdealSheafData) {M N : X.Modules} (f : M ⟶ N) (q : ℤ) :
    ((filtration I N).stage q).Factors (((filtration I M).stage q).arrow ≫ f) := sorry

/-- The functor sending a scheme module to its ideal-power filtered object. -/
noncomputable def filtered (I : X.IdealSheafData) :
    X.Modules ⥤ FilteredObject X.Modules where
  obj M :=
    { obj := M
      filtration := filtration I M }
  map f :=
    { hom := f
      preserves := map_preserves I f }
  map_id := sorry
  map_comp := sorry

/-- The ideal-power filtration functor preserves zero morphisms. -/
instance filtered_preservesZeroMorphisms (I : X.IdealSheafData) :
    (filtered I).PreservesZeroMorphisms := sorry

/-- The underlying object of the ideal-power filtered module is the original module. -/
theorem filtered_obj (I : X.IdealSheafData) (M : X.Modules) :
    ((filtered I).obj M).obj = M := sorry

/-- The underlying morphism of the ideal-power filtered map is the original morphism. -/
theorem filtered_map_hom (I : X.IdealSheafData) {M N : X.Modules} (f : M ⟶ N) :
    ((filtered I).map f).hom = f := sorry

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
      comm' := sorry }
  inv :=
    { f := fun _ ↦ 𝟙 _
      comm' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `underlyingIso` is degreewise the identity. -/
theorem underlyingIso_hom_f (I : X.IdealSheafData) (K : CochainComplex X.Modules ℤ)
    (i : ℤ) :
    (underlyingIso I K).hom.f i = 𝟙 (K.X i) := sorry

/-- The term in degree `i` of the natural-number stage `n` is the object underlying
`I ^ n K.X i`. -/
theorem stage_X (I : X.IdealSheafData) (K : CochainComplex X.Modules ℤ)
    (n : ℕ) (i : ℤ) :
    (HomologicalComplex.Filtered.Stage.complex (filtered I K) (n : ℤ)).X i =
      (idealPowerProductSubobject I (K.X i) n : X.Modules) := sorry

/-- The map from a natural-number filtration stage to the underlying complex is the termwise
ideal-power inclusion. -/
theorem stage_inclusion_f (I : X.IdealSheafData) (K : CochainComplex X.Modules ℤ)
    (n : ℕ) (i : ℤ) :
    (HomologicalComplex.Filtered.Stage.inclusion (filtered I K) (n : ℤ)).f i =
      (((filtered I K).X i).filtration.stage (n : ℤ)).arrow := sorry

end IdealPowerComplex

end AlgebraicGeometry.Scheme.Modules
