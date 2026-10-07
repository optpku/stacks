module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import stacks_project.Chap65.Lemma_65_12_2
public import stacks_project.Chap66.Definition_66_18_1_Site
public import stacks_project.Chap66.Lemma_66_26_3_Glueing
public import stacks_project.Chap76.Lemma_76_5_3_Map

/-!
# Transitivity for conormal sheaves of immersions of algebraic spaces

For composable immersions `Z ⟶ Y ⟶ X` of algebraic spaces, the canonical
conormal comparison maps form the transitivity sequence

  i^* C_{Y/X} ⟶ C_{Z/X} ⟶ C_{Z/Y} ⟶ 0.

The comparison maps and their short complex are explicit data; exactness,
epimorphy, and étale-local splitting are recorded separately.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Transitivity

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}

/-- The canonical map `(Modules.pullback i).obj (conormalSheaf j) ⟶ conormalSheaf (i ≫ j)`
for composable immersions of algebraic spaces. -/
noncomputable def baseChange (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    (Modules.pullback i).obj (conormalSheaf j) ⟶ conormalSheaf (i ≫ j) :=
  map (⟨Eq.symm (Category.comp_id (i ≫ j))⟩ : CommSq i (i ≫ j) j (𝟙 X))

/-- `baseChange` is the conormal comparison of the identity square on `X`. -/
theorem baseChange_eq (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    baseChange i j =
      map (⟨Eq.symm (Category.comp_id (i ≫ j))⟩ : CommSq i (i ≫ j) j (𝟙 X)) :=
  sorry

/-- The canonical map `conormalSheaf (i ≫ j) ⟶ conormalSheaf i` for composable immersions
of algebraic spaces. -/
noncomputable def projection (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    conormalSheaf (i ≫ j) ⟶ conormalSheaf i :=
  (SmallEtaleModuleGlueing.modulesPullbackId Z).inv.app (conormalSheaf (i ≫ j)) ≫
    map (⟨Category.id_comp (i ≫ j)⟩ : CommSq (𝟙 Z) i (i ≫ j) j)

/-- `projection` is identity-pullback transport of the conormal comparison of the identity
square on `Z`. -/
theorem projection_eq (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    projection i j =
      (SmallEtaleModuleGlueing.modulesPullbackId Z).inv.app (conormalSheaf (i ≫ j)) ≫
        map (⟨Category.id_comp (i ≫ j)⟩ : CommSq (𝟙 Z) i (i ≫ j) j) :=
  sorry

/-- The canonical conormal transitivity maps have zero composite. -/
theorem baseChange_comp_projection (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j] :
    baseChange i j ≫ projection i j = 0 :=
  sorry

/-- The canonical conormal transitivity short complex for composable immersions of
algebraic spaces. -/
noncomputable def complex (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    ShortComplex Z.Modules :=
  ShortComplex.mk (baseChange i j) (projection i j) (baseChange_comp_projection i j)

/-- `complex` is the short complex on `baseChange` and `projection`. -/
theorem complex_eq (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    complex i j =
      ShortComplex.mk (baseChange i j) (projection i j)
        (baseChange_comp_projection i j) :=
  sorry

/-- The canonical conormal transitivity short complex of two immersions of algebraic
spaces is exact. -/
theorem exact (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    (complex i j).Exact :=
  sorry

/-- The projection in the conormal transitivity sequence of two immersions of algebraic
spaces is an epimorphism. -/
instance projection_epi (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    Epi (projection i j) :=
  sorry

/-- For two composable immersions of algebraic spaces, the canonical conormal transitivity
complex is exact and its projection is an epimorphism. -/
theorem exact_and_epi (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    (complex i j).Exact ∧ Epi (projection i j) :=
  sorry

/-- The canonical conormal transitivity complex of two immersions of algebraic spaces is
short exact and splits after pullback to some covering family in `Z_étale`. -/
def IsShortExactLocallySplit (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j] : Prop :=
  (complex i j).ShortExact ∧
    ∃ (I : Type u) (U : I → smallEtaleSite Z),
      (smallEtaleTopology Z).CoversTop U ∧
        ∀ k : I, Nonempty (((complex i j).map (Modules.pullback (U k).hom)).Splitting)

/-- Short exactness together with an étale covering family on which the pulled-back complex
splits characterizes a locally split conormal transitivity complex. -/
theorem isShortExactLocallySplit_iff (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j] :
    IsShortExactLocallySplit i j ↔
      (complex i j).ShortExact ∧
        ∃ (I : Type u) (U : I → smallEtaleSite Z),
          (smallEtaleTopology Z).CoversTop U ∧
            ∀ k : I,
              Nonempty (((complex i j).map (Modules.pullback (U k).hom)).Splitting) :=
  sorry

/-- A locally split conormal transitivity complex is short exact and splits after pullback
along some covering family in the small étale site of `Z`. -/
theorem IsShortExactLocallySplit.spec (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j] (h : IsShortExactLocallySplit i j) :
    (complex i j).ShortExact ∧
      ∃ (I : Type u) (U : I → smallEtaleSite Z),
        (smallEtaleTopology Z).CoversTop U ∧
          ∀ k : I, Nonempty (((complex i j).map (Modules.pullback (U k).hom)).Splitting) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Transitivity

