/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.Category

/-!
# Vector bundles and quasicoherent modules

This file records the anti-equivalence between vector bundles over a scheme and
quasicoherent modules on that scheme.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- The degree-one module of a vector bundle, regarded as a quasicoherent module. -/
noncomputable def vectorBundleDegreeOne (S : Scheme.{u})
    (E : VectorBundleOver S) : QCoh S :=
  ⟨E.pushforwardGrading.degreePiece 1, by sorry⟩

/-- The degree-one module map induced by a morphism of vector bundles. -/
noncomputable def vectorBundleDegreeOneMap (S : Scheme.{u})
    {E E' : VectorBundleOver S} (f : VectorBundleHom S E E') :
    vectorBundleDegreeOne S E' ⟶ vectorBundleDegreeOne S E :=
  ObjectProperty.homMk
    (GradedQcAlgebra.degreeMap S
      (ConeOver.chosenAlgebraPullback S f.hom f.overBase) 1)

@[simp]
theorem vectorBundleDegreeOneMap_hom (S : Scheme.{u})
    {E E' : VectorBundleOver S} (f : VectorBundleHom S E E') :
    (vectorBundleDegreeOneMap S f).hom =
      GradedQcAlgebra.degreeMap S
        (ConeOver.chosenAlgebraPullback S f.hom f.overBase) 1 :=
  rfl

/-- The anti-variant degree-one functor from vector bundles to quasicoherent modules. -/
noncomputable def vectorBundleOverOpToQCoh (S : Scheme.{u}) :
    (vectorBundleCat S)ᵒᵖ ⥤ QCoh S where
  obj E := vectorBundleDegreeOne S E.unop
  map f := vectorBundleDegreeOneMap S f.unop
  map_id := by sorry
  map_comp := by sorry

@[simp]
theorem vectorBundleOverOpToQCoh_obj (S : Scheme.{u})
    (E : (vectorBundleCat S)ᵒᵖ) :
    (vectorBundleOverOpToQCoh S).obj E = vectorBundleDegreeOne S E.unop :=
  rfl

@[simp]
theorem vectorBundleOverOpToQCoh_map (S : Scheme.{u})
    {E E' : (vectorBundleCat S)ᵒᵖ} (f : E ⟶ E') :
    (vectorBundleOverOpToQCoh S).map f = vectorBundleDegreeOneMap S f.unop :=
  rfl

/-- The source-level equivalence assertion for the canonical degree-one functor. -/
instance vectorBundleOverOpToQCoh_isEquivalence (S : Scheme.{u}) :
    (vectorBundleOverOpToQCoh S).IsEquivalence := by
  sorry

/-- The category of vector bundles over a scheme is anti-equivalent to its category of
quasicoherent modules. -/
noncomputable def vectorBundleOverOpEquivQCoh (S : Scheme.{u}) :
    (vectorBundleCat S)ᵒᵖ ≌ QCoh S :=
  (vectorBundleOverOpToQCoh S).asEquivalence

@[simp]
theorem vectorBundleOverOpEquivQCoh_functor (S : Scheme.{u}) :
    (vectorBundleOverOpEquivQCoh S).functor = vectorBundleOverOpToQCoh S :=
  rfl

end AlgebraicGeometry.Scheme
