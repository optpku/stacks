/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Transitivity
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Deformation.Action
public import ReasLib.CategoryTheory.Sites.Torsor.IsoClasses

/-!
# Base change for infinitesimal deformations of scheme morphisms

For a cartesian change through a thickened base, the conormal comparison determines the
compatible conormal map. The deformation sheaf can then be described using restrictions of
lifts and carries the transported action of the relative differential parameter sheaf.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.MonoidalClosed
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.Deformation

variable {Z Z' X X' Y Y' : Scheme.{u}}
variable {j : Y ⟶ Y'}

/-- The conormal comparison obtained by pulling the cartesian base-change comparison back
along `a`. -/
noncomputable def baseConormalMap (a : X ⟶ Y) [X.Over Z] [Y.Over Z] [Z.Over Z']
    [Y'.Over Z'] [a.IsOver Z] (sqY : CommSq (Y ↘ Z) j (Z ↘ Z') (Y' ↘ Z')) :
    (Scheme.Modules.pullback (X ↘ Z)).obj (Scheme.Hom.conormalSheaf (Z ↘ Z')) ⟶
      (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) :=
  (Scheme.Modules.pullbackCongr (comp_over a Z)).inv.app _ ≫
    (Scheme.Modules.pullbackComp a (Y ↘ Z)).inv.app _ ≫
      (Scheme.Modules.pullback a).map (Scheme.Hom.Conormal.map sqY)

/-- The defining composite for the pulled-back cartesian conormal comparison. -/
theorem baseConormalMap_def (a : X ⟶ Y) [X.Over Z] [Y.Over Z] [Z.Over Z']
    [Y'.Over Z'] [a.IsOver Z] (sqY : CommSq (Y ↘ Z) j (Z ↘ Z') (Y' ↘ Z')) :
    baseConormalMap a sqY =
      (Scheme.Modules.pullbackCongr (comp_over a Z)).inv.app _ ≫
        (Scheme.Modules.pullbackComp a (Y ↘ Z)).inv.app _ ≫
          (Scheme.Modules.pullback a).map (Scheme.Hom.Conormal.map sqY) := sorry

/-- A cartesian thickened-base square makes the pulled-back conormal comparison epimorphic. -/
theorem baseConormalMap_epi (a : X ⟶ Y) [X.Over Z] [Y.Over Z] [Z.Over Z']
    [Y'.Over Z'] [a.IsOver Z] [IsThickening (Z ↘ Z')]
    (hY : IsPullback (Y ↘ Z) j (Z ↘ Z') (Y' ↘ Z')) :
    Epi (baseConormalMap a hY.toCommSq) := sorry

/-- For a lift over `Z'`, its conormal map composed with the base comparison is the
canonical conormal map induced from the corresponding square over `Z'`. -/
theorem baseConormalMap_comp (i : X ⟶ X') (j : Y ⟶ Y') (a : X ⟶ Y)
    (a' : X' ⟶ Y') [X.Over Z] [Y.Over Z] [Z.Over Z'] [X'.Over Z'] [Y'.Over Z']
    [a.IsOver Z] (hY : IsPullback (Y ↘ Z) j (Z ↘ Z') (Y' ↘ Z'))
    (sqX : CommSq (X ↘ Z) i (Z ↘ Z') (X' ↘ Z'))
    (sq : CommSq a i j a') [a'.IsOver Z'] :
    baseConormalMap a hY.toCommSq ≫ Scheme.Hom.Conormal.map sq =
      Scheme.Hom.Conormal.map sqX := sorry

/-- Precomposition with the pulled-back transitivity projection, followed by forgetting module
structure and pushforward along `i`, compares the two deformation-parameter sheaves. -/
noncomputable def parameterChange (Z Z' : Scheme.{u}) (i : X ⟶ X') (a : X ⟶ Y)
    [X.Over Z] [X.Over Z'] [Y.Over Z] [Y.Over Z'] [Z.Over Z']
    [IsOverTower Y Z Z'] [a.IsOver Z] [a.IsOver Z'] :
    parameterSheaf Z i a ⟶ parameterSheaf Z' i a :=
  (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).map
    ((SheafOfModules.toSheaf X.ringCatSheaf).map
      ((MonoidalClosed.pre
        ((Scheme.Modules.pullback a).map
          (RelativeDifferentials.Transitivity.projection Y Z Z'))).app
            (Scheme.Hom.conormalSheaf i)))

/-- The component of `parameterChange` is precomposition by the pulled-back transitivity
projection, followed by the canonical forgetful and pushforward functors. -/
theorem parameterChange_app (Z Z' : Scheme.{u}) (i : X ⟶ X') (a : X ⟶ Y)
    [X.Over Z] [X.Over Z'] [Y.Over Z] [Y.Over Z'] [Z.Over Z']
    [IsOverTower Y Z Z'] [a.IsOver Z] [a.IsOver Z'] (U' : X'.Opens) :
    (parameterChange Z Z' i a).1.app (op U') =
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map
            ((MonoidalClosed.pre
              ((Scheme.Modules.pullback a).map
                (RelativeDifferentials.Transitivity.projection Y Z Z'))).app
                  (Scheme.Hom.conormalSheaf i)))).1.app (op U') := sorry

/-- For a thickened base, the comparison between the deformation-parameter sheaves is an
isomorphism. -/
theorem parameterChange_isIso (Z Z' : Scheme.{u}) (i : X ⟶ X') (a : X ⟶ Y)
    [X.Over Z] [X.Over Z'] [Y.Over Z] [Y.Over Z'] [Z.Over Z']
    [IsOverTower Y Z Z'] [IsThickening (Z ↘ Z')] [a.IsOver Z] [a.IsOver Z'] :
    IsIso (parameterChange Z Z' i a) := sorry

/-- The action of `Hom(a^* Ω[Y/Z], C[X/X'])` on a deformation section, obtained by
mapping its parameter to the existing `Z'`-relative deformation action. -/
noncomputable def relativeBaseAct (Z Z' : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) [X.Over Z] [X.Over Z'] [X'.Over Z'] [Y.Over Z] [Y.Over Z']
    [Y'.Over Z'] [Z.Over Z'] [IsOverTower Y Z Z'] [IsFirstOrderThickening i]
    [IsFirstOrderThickening j] [i.IsOver Z'] [j.IsOver Z'] [a.IsOver Z] [a.IsOver Z']
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i) (U' : X'.Opens)
    (theta : (parameterSheaf Z i a).1.obj (op U'))
    (s : sections Z' i j a A U') : sections Z' i j a A U' :=
  act Z' i j a A U' ((parameterChange Z Z' i a).1.app (op U') theta) s

/-- The relative-base action fixes a deformation section at the zero parameter. -/
theorem relativeBaseAct_zero (Z Z' : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) [X.Over Z] [X.Over Z'] [X'.Over Z'] [Y.Over Z] [Y.Over Z']
    [Y'.Over Z'] [Z.Over Z'] [IsOverTower Y Z Z'] [IsFirstOrderThickening i]
    [IsFirstOrderThickening j] [i.IsOver Z'] [j.IsOver Z'] [a.IsOver Z] [a.IsOver Z']
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i) (U' : X'.Opens) (s : sections Z' i j a A U') :
    relativeBaseAct Z Z' i j a A U' 0 s = s := sorry

/-- Acting by a sum of relative-base parameters is successive action. -/
theorem relativeBaseAct_add (Z Z' : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) [X.Over Z] [X.Over Z'] [X'.Over Z'] [Y.Over Z] [Y.Over Z']
    [Y'.Over Z'] [Z.Over Z'] [IsOverTower Y Z Z'] [IsFirstOrderThickening i]
    [IsFirstOrderThickening j] [i.IsOver Z'] [j.IsOver Z'] [a.IsOver Z] [a.IsOver Z']
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i) (U' : X'.Opens)
    (theta eta : (parameterSheaf Z i a).1.obj (op U'))
    (s : sections Z' i j a A U') :
    relativeBaseAct Z Z' i j a A U' (theta + eta) s =
      relativeBaseAct Z Z' i j a A U' theta
        (relativeBaseAct Z Z' i j a A U' eta s) := sorry

/-- The relative-base action commutes with restriction to smaller opens. -/
theorem relativeBaseAct_naturality (Z Z' : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) [X.Over Z] [X.Over Z'] [X'.Over Z'] [Y.Over Z] [Y.Over Z']
    [Y'.Over Z'] [Z.Over Z'] [IsOverTower Y Z Z'] [IsFirstOrderThickening i]
    [IsFirstOrderThickening j] [i.IsOver Z'] [j.IsOver Z'] [a.IsOver Z] [a.IsOver Z']
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i) {U' V' : X'.Opens} (h : V' ≤ U')
    (theta : (parameterSheaf Z i a).1.obj (op U')) (s : sections Z' i j a A U') :
    restrictSection Z' i j a A h (relativeBaseAct Z Z' i j a A U' theta s) =
      relativeBaseAct Z Z' i j a A V'
        ((parameterSheaf Z i a).1.map (homOfLE h).op theta)
        (restrictSection Z' i j a A h s) := sorry

/-- The sectionwise multiplicative presentation of the relative-base additive action. -/
@[implicit_reducible]
noncomputable def relativeBaseMulAction (Z Z' : Scheme.{u}) (i : X ⟶ X')
    (j : Y ⟶ Y') (a : X ⟶ Y) [X.Over Z] [X.Over Z'] [X'.Over Z']
    [Y.Over Z] [Y.Over Z'] [Y'.Over Z'] [Z.Over Z'] [IsOverTower Y Z Z']
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver Z'] [j.IsOver Z'] [a.IsOver Z] [a.IsOver Z']
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i) (U' : X'.Opens) :
    MulAction ((CategoryTheory.Sheaf.toSheafOfGroups
      (parameterSheaf Z i a)).1.obj (op U'))
      ((sheaf Z' i j a A).1.obj (op U')) where
  smul := relativeBaseAct Z Z' i j a A U'
  one_smul := relativeBaseAct_zero Z Z' i j a A U'
  mul_smul := relativeBaseAct_add Z Z' i j a A U'

/-- The relative-base deformation action is pretransitive on every open. -/
theorem relativeBaseMulAction_isPretransitive (Z Z' : Scheme.{u}) (i : X ⟶ X')
    (j : Y ⟶ Y') (a : X ⟶ Y) [X.Over Z] [X.Over Z'] [X'.Over Z']
    [Y.Over Z] [Y.Over Z'] [Y'.Over Z'] [Z.Over Z'] [IsOverTower Y Z Z']
    [IsThickening (Z ↘ Z')] [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver Z'] [j.IsOver Z'] [a.IsOver Z] [a.IsOver Z']
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i)
    (U' : X'.Opens) :
    @MulAction.IsPretransitive
      ((CategoryTheory.Sheaf.toSheafOfGroups (parameterSheaf Z i a)).1.obj (op U'))
      ((sheaf Z' i j a A).1.obj (op U'))
      (relativeBaseMulAction Z Z' i j a A U').toSMul := sorry

/-- The relative-base deformation action is free on every open. -/
theorem relativeBaseMulAction_isCancelSMul (Z Z' : Scheme.{u}) (i : X ⟶ X')
    (j : Y ⟶ Y') (a : X ⟶ Y) [X.Over Z] [X.Over Z'] [X'.Over Z']
    [Y.Over Z] [Y.Over Z'] [Y'.Over Z'] [Z.Over Z'] [IsOverTower Y Z Z']
    [IsThickening (Z ↘ Z')] [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver Z'] [j.IsOver Z'] [a.IsOver Z] [a.IsOver Z']
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i)
    (U' : X'.Opens) :
    @IsCancelSMul
      ((CategoryTheory.Sheaf.toSheafOfGroups (parameterSheaf Z i a)).1.obj (op U'))
      ((sheaf Z' i j a A).1.obj (op U'))
      (relativeBaseMulAction Z Z' i j a A U').toSMul := sorry

/-- The deformation sheaf over `Z'`, viewed as a pseudo-torsor under the relative-base
parameter sheaf formed with `Ω[Y/Z]`. -/
noncomputable def relativeBasePseudoTorsor (Z Z' : Scheme.{u}) (i : X ⟶ X')
    (j : Y ⟶ Y') (a : X ⟶ Y) [X.Over Z] [X.Over Z'] [X'.Over Z']
    [Y.Over Z] [Y.Over Z'] [Y'.Over Z'] [Z.Over Z'] [IsOverTower Y Z Z']
    [IsThickening (Z ↘ Z')] [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver Z'] [j.IsOver Z'] [a.IsOver Z] [a.IsOver Z']
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i) :
    CategoryTheory.Sheaf.PseudoTorsor
      (CategoryTheory.Sheaf.toSheafOfGroups (parameterSheaf Z i a)) where
  carrier := sheaf Z' i j a A
  mulAction := relativeBaseMulAction Z Z' i j a A
  act_naturality f theta s := relativeBaseAct_naturality Z Z' i j a A f.le theta s
  isPretransitive := relativeBaseMulAction_isPretransitive Z Z' i j a A
  isCancelSMul := relativeBaseMulAction_isCancelSMul Z Z' i j a A

/-- The carrier of the relative-base pseudo-torsor is the deformation sheaf. -/
theorem relativeBasePseudoTorsor_carrier (Z Z' : Scheme.{u}) (i : X ⟶ X')
    (j : Y ⟶ Y') (a : X ⟶ Y) [X.Over Z] [X.Over Z'] [X'.Over Z']
    [Y.Over Z] [Y.Over Z'] [Y'.Over Z'] [Z.Over Z'] [IsOverTower Y Z Z']
    [IsThickening (Z ↘ Z')] [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver Z'] [j.IsOver Z'] [a.IsOver Z] [a.IsOver Z']
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i) :
    (relativeBasePseudoTorsor Z Z' i j a A).carrier =
      sheaf Z' i j a A := sorry

/-- The action stored by the relative-base pseudo-torsor is `relativeBaseAct`. -/
theorem relativeBasePseudoTorsor_smul (Z Z' : Scheme.{u}) (i : X ⟶ X')
    (j : Y ⟶ Y') (a : X ⟶ Y) [X.Over Z] [X.Over Z'] [X'.Over Z']
    [Y.Over Z] [Y.Over Z'] [Y'.Over Z'] [Z.Over Z'] [IsOverTower Y Z Z']
    [IsThickening (Z ↘ Z')] [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver Z'] [j.IsOver Z'] [a.IsOver Z] [a.IsOver Z']
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i)
    (U' : X'.Opens)
    (theta : (parameterSheaf Z i a).1.obj (op U')) (s : sections Z' i j a A U') :
    ((relativeBasePseudoTorsor Z Z' i j a A).mulAction U').smul theta s =
      relativeBaseAct Z Z' i j a A U' theta s := sorry

/-- For a cartesian change through a thickened base, a compatible conormal map is determined
by its composite with the pulled-back base conormal comparison. -/
theorem conormalMap_ext (i : X ⟶ X') (j : Y ⟶ Y') (a : X ⟶ Y)
    [X.Over Z] [X.Over Z'] [X'.Over Z'] [Y.Over Z] [Y.Over Z'] [Y'.Over Z']
    [Z.Over Z'] [IsOverTower X Z Z'] [IsOverTower Y Z Z']
    [IsThickening (Z ↘ Z')] [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver Z'] [j.IsOver Z'] [a.IsOver Z] [a.IsOver Z']
    (hY : IsPullback (Y ↘ Z) j (Z ↘ Z') (Y' ↘ Z'))
    (sqX : CommSq (X ↘ Z) i (Z ↘ Z') (X' ↘ Z'))
    (A B : (Modules.pullback a).obj (conormalSheaf j) ⟶ conormalSheaf i)
    (hA : baseConormalMap a hY.toCommSq ≫ A = Conormal.map sqX)
    (hB : baseConormalMap a hY.toCommSq ≫ B = Conormal.map sqX) :
    A = B := sorry

/-- For a cartesian change through a thickened base, a local deformation section is exactly a
`Z'`-morphism whose restriction to the closed subscheme agrees with the original morphism. -/
theorem mem_sections_iff_of_isPullback (i : X ⟶ X') (j : Y ⟶ Y') (a : X ⟶ Y)
    [X.Over Z] [X.Over Z'] [X'.Over Z'] [Y.Over Z] [Y.Over Z'] [Y'.Over Z']
    [Z.Over Z'] [IsOverTower X Z Z'] [IsOverTower Y Z Z']
    [IsThickening (Z ↘ Z')] [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver Z'] [j.IsOver Z'] [a.IsOver Z] [a.IsOver Z']
    (hY : IsPullback (Y ↘ Z) j (Z ↘ Z') (Y' ↘ Z'))
    (sqX : CommSq (X ↘ Z) i (Z ↘ Z') (X' ↘ Z'))
    (A : (Modules.pullback a).obj (conormalSheaf j) ⟶ conormalSheaf i)
    (hA : baseConormalMap a hY.toCommSq ≫ A = Conormal.map sqX)
    (U' : X'.Opens) (a' : U'.toScheme ⟶ Y') :
    a' ∈ sections Z' i j a A U' ↔
      a' ≫ (Y' ↘ Z') = U'.ι ≫ (X' ↘ Z') ∧
        CommSq ((i ⁻¹ᵁ U').ι ≫ a) (i ∣_ U') j a' := sorry

/-- The relative differential parameter sheaf acts simply transitively on every nonempty set
of local lifts in the cartesian-base deformation sheaf. -/
theorem relativeBaseAct_simplyTransitive (i : X ⟶ X') (j : Y ⟶ Y') (a : X ⟶ Y)
    [X.Over Z] [X.Over Z'] [X'.Over Z'] [Y.Over Z] [Y.Over Z'] [Y'.Over Z']
    [Z.Over Z'] [IsOverTower X Z Z'] [IsOverTower Y Z Z']
    [IsThickening (Z ↘ Z')] [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver Z'] [j.IsOver Z'] [a.IsOver Z] [a.IsOver Z']
    (hY : IsPullback (Y ↘ Z) j (Z ↘ Z') (Y' ↘ Z'))
    (sqX : CommSq (X ↘ Z) i (Z ↘ Z') (X' ↘ Z'))
    (A : (Modules.pullback a).obj (conormalSheaf j) ⟶ conormalSheaf i)
    (hA : baseConormalMap a hY.toCommSq ≫ A = Conormal.map sqX)
    (U' : X'.Opens) (s : sections Z' i j a A U') :
    Function.Bijective (fun theta : (parameterSheaf Z i a).1.obj (op U') ↦
      relativeBaseAct Z Z' i j a A U' theta s) := sorry

end AlgebraicGeometry.Scheme.Hom.Deformation
