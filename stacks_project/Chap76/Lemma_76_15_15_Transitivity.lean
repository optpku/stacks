module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import stacks_project.Chap66.Lemma_66_26_3_Glueing
public import stacks_project.Chap76.Lemma_76_15_15_ComparisonPullback

/-!
# Conormal transitivity for formally unramified morphisms of algebraic spaces

The Lemma 76.15.8 comparisons of conormal sheaves along the identity square on
`X` and the identity square on `Z` yield a right-exact sequence
`i^* C_{Y/X} ⟶ C_{Z/X} ⟶ C_{Z/Y} ⟶ 0` for formally unramified
`Z ⟶ Y ⟶ X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
namespace Transitivity

variable {S : Scheme.{u}} {X Y Z Z' Y' : AlgebraicSpace S}
variable (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iY : Y ⟶ Y') (fY : Y' ⟶ X)
variable (i : Z ⟶ Y)
variable [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iY fY]
variable [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iY ≫ fY)]
variable (sq : CommSq i (iZ ≫ fZ) (iY ≫ fY) (𝟙 X))

/-- The first arrow `i^* C_{Y/X} ⟶ C_{Z/X}` of the transitivity sequence, as the
Lemma 76.15.8 conormal map of the identity square on `X`. -/
noncomputable def baseChange :
    (Modules.pullback i).obj (Hom.conormalSheaf iY) ⟶ Hom.conormalSheaf iZ :=
  conormalMap iZ fZ iY fY i (𝟙 X) sq

/-- `baseChange` is the Lemma 76.15.8 conormal map of the identity square on `X`. -/
theorem baseChange_eq :
    baseChange iZ fZ iY fY i sq = conormalMap iZ fZ iY fY i (𝟙 X) sq :=
  sorry

/-- The second arrow `C_{Z/X} ⟶ C_{Z/Y}` of the transitivity sequence, as identity
pullback transport of the Lemma 76.15.8 conormal map of the identity square on
`Z`. -/
noncomputable def projection [FormallyUnramified i] :
    Hom.conormalSheaf iZ ⟶
      Hom.conormalSheaf (comparisonPullbackHom iZ fZ iY fY i sq) :=
  let sqZ :
      CommSq (𝟙 Z)
        (comparisonPullbackHom iZ fZ iY fY i sq ≫
          pullback.fst iY (comparison iZ fZ iY fY i (𝟙 X) sq))
        (iZ ≫ fZ) (iY ≫ fY) :=
    ⟨(Category.id_comp (iZ ≫ fZ)).trans
        ((sq.w.trans (Category.comp_id (iZ ≫ fZ))).symm.trans
          (congrArg (fun k ↦ k ≫ iY ≫ fY)
            (pullback.lift_fst i iZ
              (comparison_comp iZ fZ iY fY i (𝟙 X) sq)).symm))⟩
  (SmallEtaleModuleGlueing.modulesPullbackId Z).inv.app (Hom.conormalSheaf iZ) ≫
    conormalMap (comparisonPullbackHom iZ fZ iY fY i sq)
      (pullback.fst iY (comparison iZ fZ iY fY i (𝟙 X) sq)) iZ fZ (𝟙 Z)
      (iY ≫ fY) sqZ

/-- `projection` is identity-pullback transport of the Lemma 76.15.8 conormal map of
the identity square on `Z`. -/
theorem projection_eq [FormallyUnramified i] :
    projection iZ fZ iY fY i sq =
      (SmallEtaleModuleGlueing.modulesPullbackId Z).inv.app (Hom.conormalSheaf iZ) ≫
        conormalMap (comparisonPullbackHom iZ fZ iY fY i sq)
          (pullback.fst iY (comparison iZ fZ iY fY i (𝟙 X) sq)) iZ fZ (𝟙 Z)
          (iY ≫ fY)
          ⟨(Category.id_comp (iZ ≫ fZ)).trans
              ((sq.w.trans (Category.comp_id (iZ ≫ fZ))).symm.trans
                (congrArg (fun k ↦ k ≫ iY ≫ fY)
                  (pullback.lift_fst i iZ
                    (comparison_comp iZ fZ iY fY i (𝟙 X) sq)).symm))⟩ :=
  sorry

/-- The canonical transitivity maps have zero composite. -/
theorem baseChange_comp_projection [FormallyUnramified i] :
    baseChange iZ fZ iY fY i sq ≫ projection iZ fZ iY fY i sq = 0 :=
  sorry

/-- The canonical conormal transitivity short complex of formally unramified
`Z ⟶ Y ⟶ X`. -/
noncomputable def complex [FormallyUnramified i] : ShortComplex Z.Modules :=
  ShortComplex.mk (baseChange iZ fZ iY fY i sq) (projection iZ fZ iY fY i sq)
    (baseChange_comp_projection iZ fZ iY fY i sq)

/-- `complex` is the short complex on `baseChange` and `projection`. -/
theorem complex_eq [FormallyUnramified i] :
    complex iZ fZ iY fY i sq =
      ShortComplex.mk (baseChange iZ fZ iY fY i sq) (projection iZ fZ iY fY i sq)
        (baseChange_comp_projection iZ fZ iY fY i sq) :=
  sorry

/-- The canonical conormal transitivity short complex of formally unramified
`Z ⟶ Y ⟶ X` is exact. -/
theorem exact [FormallyUnramified i] : (complex iZ fZ iY fY i sq).Exact :=
  sorry

/-- The projection `C_{Z/X} ⟶ C_{Z/Y}` in the transitivity sequence is an
epimorphism. -/
instance projection_epi [FormallyUnramified i] :
    Epi (projection iZ fZ iY fY i sq) :=
  sorry

/-- For formally unramified `Z ⟶ Y ⟶ X`, the canonical sequence
`i^* C_{Y/X} ⟶ C_{Z/X} ⟶ C_{Z/Y} ⟶ 0` is exact. -/
theorem exact_and_epi [FormallyUnramified i] :
    (complex iZ fZ iY fY i sq).Exact ∧ Epi (projection iZ fZ iY fY i sq) :=
  sorry

end Transitivity
end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
