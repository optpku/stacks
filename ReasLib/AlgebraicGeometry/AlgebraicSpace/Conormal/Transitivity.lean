/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Functorial
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Glueing

/-!
# Transitivity for conormal sheaves of immersions of algebraic spaces

For composable immersions of algebraic spaces, the canonical conormal comparison
maps form a short complex whose exactness and epimorphy are recorded here.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Transitivity

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}

/-- The canonical map from the pullback of the conormal sheaf of `j` to that of `i ≫ j`. -/
noncomputable def baseChange (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    (Modules.pullback i).obj (conormalSheaf j) ⟶ conormalSheaf (i ≫ j) :=
  map (⟨Eq.symm (Category.comp_id (i ≫ j))⟩ : CommSq i (i ≫ j) j (𝟙 X))

/-- The defining commutative-square formula for `baseChange`. -/
theorem baseChange_eq (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    baseChange i j =
      map (⟨Eq.symm (Category.comp_id (i ≫ j))⟩ : CommSq i (i ≫ j) j (𝟙 X)) :=
  rfl

/-- The canonical map from the conormal sheaf of `i ≫ j` to that of `i`. -/
noncomputable def projection (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    conormalSheaf (i ≫ j) ⟶ conormalSheaf i :=
  (SmallEtaleModuleGlueing.modulesPullbackId Z).inv.app (conormalSheaf (i ≫ j)) ≫
    map (⟨Category.id_comp (i ≫ j)⟩ : CommSq (𝟙 Z) i (i ≫ j) j)

/-- The defining identity-pullback formula for `projection`. -/
theorem projection_eq (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    projection i j =
      (SmallEtaleModuleGlueing.modulesPullbackId Z).inv.app (conormalSheaf (i ≫ j)) ≫
        map (⟨Category.id_comp (i ≫ j)⟩ : CommSq (𝟙 Z) i (i ≫ j) j) :=
  rfl

/-- The canonical conormal transitivity maps have zero composite. -/
theorem baseChange_comp_projection (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j] :
    baseChange i j ≫ projection i j = 0 :=
  sorry

/-- The canonical conormal transitivity short complex for two composable immersions. -/
noncomputable def complex (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    ShortComplex Z.Modules :=
  ShortComplex.mk (baseChange i j) (projection i j) (baseChange_comp_projection i j)

/-- The defining short-complex formula for `complex`. -/
theorem complex_eq (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    complex i j =
      ShortComplex.mk (baseChange i j) (projection i j)
        (baseChange_comp_projection i j) :=
  rfl

/-- The canonical conormal transitivity short complex is exact. -/
theorem exact (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    (complex i j).Exact :=
  sorry

/-- The projection in the canonical conormal transitivity sequence is an epimorphism. -/
instance projection_epi (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    Epi (projection i j) :=
  sorry

/-- The canonical conormal transitivity complex is exact and its projection is epic. -/
theorem exact_and_epi (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    (complex i j).Exact ∧ Epi (projection i j) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Transitivity
