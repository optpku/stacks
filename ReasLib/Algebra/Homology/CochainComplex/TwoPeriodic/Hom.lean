/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic

@[expose] public section

open CategoryTheory Limits

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- A morphism of two-periodic endomorphism complexes is one map commuting with both
differentials. -/
structure Hom (K L : TwoPeriodicEndomorphism C) where
  /-- The underlying morphism in the ambient category. -/
  hom : K.X ⟶ L.X
  /-- Compatibility with the differential from degree `0` to degree `1`. -/
  comm₀ : hom ≫ L.d₀ = K.d₀ ≫ hom
  /-- Compatibility with the differential from degree `1` to degree `0`. -/
  comm₁ : hom ≫ L.d₁ = K.d₁ ≫ hom

namespace Hom

/-- A periodic morphism commutes with the differential of the associated cochain complexes. -/
theorem comm_differential {K L : TwoPeriodicEndomorphism C} (f : Hom K L)
    (i j : ZMod 2) :
    f.hom ≫ L.toCochainComplex.d i j = K.toCochainComplex.d i j ≫ f.hom := by
  dsimp only [toCochainComplex]
  by_cases hij : i + 1 = j
  · subst j
    simp only [CochainComplex.of_d]
    split_ifs with hi
    · exact f.comm₀
    · exact f.comm₁
  · simp only [CochainComplex.of_d_ne _ _ hij, comp_zero, zero_comp]

/-- The morphism of `ZMod 2`-indexed cochain complexes associated to a periodic morphism. -/
def toCochainComplexHom {K L : TwoPeriodicEndomorphism C} (f : Hom K L) :
    K.toCochainComplex ⟶ L.toCochainComplex where
  f _ := f.hom
  comm' i j _ := f.comm_differential i j

/-- Every component of the associated cochain-complex morphism is the underlying map. -/
@[simp]
theorem toCochainComplexHom_f {K L : TwoPeriodicEndomorphism C} (f : Hom K L)
    (i : ZMod 2) : f.toCochainComplexHom.f i = f.hom := by
  rfl

/-- The identity morphism of a two-periodic endomorphism complex commutes with `d₀`. -/
theorem id_comm₀ (K : TwoPeriodicEndomorphism C) :
    𝟙 K.X ≫ K.d₀ = K.d₀ ≫ 𝟙 K.X := by
  simp only [Category.id_comp, Category.comp_id]

/-- The identity morphism of a two-periodic endomorphism complex commutes with `d₁`. -/
theorem id_comm₁ (K : TwoPeriodicEndomorphism C) :
    𝟙 K.X ≫ K.d₁ = K.d₁ ≫ 𝟙 K.X := by
  simp only [Category.id_comp, Category.comp_id]

/-- The identity periodic morphism. -/
def id (K : TwoPeriodicEndomorphism C) : Hom K K where
  hom := 𝟙 K.X
  comm₀ := id_comm₀ K
  comm₁ := id_comm₁ K

/-- The composite of periodic morphisms commutes with `d₀`. -/
theorem comp_comm₀ {K L M : TwoPeriodicEndomorphism C} (f : Hom K L) (g : Hom L M) :
    (f.hom ≫ g.hom) ≫ M.d₀ = K.d₀ ≫ (f.hom ≫ g.hom) := by
  rw [Category.assoc, g.comm₀, ← Category.assoc, f.comm₀, Category.assoc]

/-- The composite of periodic morphisms commutes with `d₁`. -/
theorem comp_comm₁ {K L M : TwoPeriodicEndomorphism C} (f : Hom K L) (g : Hom L M) :
    (f.hom ≫ g.hom) ≫ M.d₁ = K.d₁ ≫ (f.hom ≫ g.hom) := by
  rw [Category.assoc, g.comm₁, ← Category.assoc, f.comm₁, Category.assoc]

/-- Composition of periodic morphisms. -/
def comp {K L M : TwoPeriodicEndomorphism C} (f : Hom K L) (g : Hom L M) : Hom K M where
  hom := f.hom ≫ g.hom
  comm₀ := comp_comm₀ f g
  comm₁ := comp_comm₁ f g

/-- Conversion to cochain-complex morphisms preserves identity morphisms. -/
theorem toCochainComplexHom_id (K : TwoPeriodicEndomorphism C) :
    (id K).toCochainComplexHom = 𝟙 K.toCochainComplex := by
  apply HomologicalComplex.hom_ext
  intro i
  rfl

/-- Conversion to cochain-complex morphisms preserves composition. -/
theorem toCochainComplexHom_comp {K L M : TwoPeriodicEndomorphism C}
    (f : Hom K L) (g : Hom L M) :
    (f.comp g).toCochainComplexHom = f.toCochainComplexHom ≫ g.toCochainComplexHom := by
  apply HomologicalComplex.hom_ext
  intro i
  rfl

end Hom

end CategoryTheory.TwoPeriodicEndomorphism
