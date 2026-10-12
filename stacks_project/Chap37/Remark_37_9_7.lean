/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Deformation.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.Deformation

/- Remark 37.9.7 (1): in a cartesian thickening of the base, the conormal map attached to a
lift is uniquely determined by its composite with the pulled-back base conormal map. -/
@[stacks 0CK2] #check
  (AlgebraicGeometry.Scheme.Hom.Deformation.conormalMap_ext :
    ∀ {Z Z' X X' Y Y' : Scheme.{u}} (i : X ⟶ X') (j : Y ⟶ Y') (a : X ⟶ Y)
      [X.Over Z] [X.Over Z'] [X'.Over Z'] [Y.Over Z] [Y.Over Z'] [Y'.Over Z']
      [Z.Over Z'] [IsOverTower X Z Z'] [IsOverTower Y Z Z']
      [IsThickening (Z ↘ Z')] [IsFirstOrderThickening i] [IsFirstOrderThickening j]
      [i.IsOver Z'] [j.IsOver Z'] [a.IsOver Z] [a.IsOver Z']
      (hY : IsPullback (Y ↘ Z) j (Z ↘ Z') (Y' ↘ Z'))
      (sqX : CommSq (X ↘ Z) i (Z ↘ Z') (X' ↘ Z'))
      (A B : (Modules.pullback a).obj (conormalSheaf j) ⟶ conormalSheaf i)
      (hA : baseConormalMap a hY.toCommSq ≫ A = Conormal.map sqX)
      (hB : baseConormalMap a hY.toCommSq ≫ B = Conormal.map sqX),
      A = B)

/- Remark 37.9.7 (2): in the cartesian-base case, a local section of the deformation sheaf
is exactly a `Z'`-morphism whose restriction to the closed subscheme agrees with `a`. -/
@[stacks 0CK2] #check
  (AlgebraicGeometry.Scheme.Hom.Deformation.mem_sections_iff_of_isPullback :
    ∀ {Z Z' X X' Y Y' : Scheme.{u}} (i : X ⟶ X') (j : Y ⟶ Y') (a : X ⟶ Y)
      [X.Over Z] [X.Over Z'] [X'.Over Z'] [Y.Over Z] [Y.Over Z'] [Y'.Over Z']
      [Z.Over Z'] [IsOverTower X Z Z'] [IsOverTower Y Z Z']
      [IsThickening (Z ↘ Z')] [IsFirstOrderThickening i] [IsFirstOrderThickening j]
      [i.IsOver Z'] [j.IsOver Z'] [a.IsOver Z] [a.IsOver Z']
      (hY : IsPullback (Y ↘ Z) j (Z ↘ Z') (Y' ↘ Z'))
      (sqX : CommSq (X ↘ Z) i (Z ↘ Z') (X' ↘ Z'))
      (A : (Modules.pullback a).obj (conormalSheaf j) ⟶ conormalSheaf i)
      (hA : baseConormalMap a hY.toCommSq ≫ A = Conormal.map sqX)
      (U' : X'.Opens) (a' : U'.toScheme ⟶ Y'),
      a' ∈ sections Z' i j a A U' ↔
        a' ≫ (Y' ↘ Z') = U'.ι ≫ (X' ↘ Z') ∧
          CommSq ((i ⁻¹ᵁ U').ι ≫ a) (i ∣_ U') j a')

/- Remark 37.9.7 (3): the sheaf `Hom_𝒪_X(a^* Ω[Y/Z], C[X/X'])` acts simply
transitively on every set of local lifts in the cartesian-base deformation sheaf. -/
@[stacks 0CK2] #check
  (AlgebraicGeometry.Scheme.Hom.Deformation.relativeBaseAct_simplyTransitive :
    ∀ {Z Z' X X' Y Y' : Scheme.{u}} (i : X ⟶ X') (j : Y ⟶ Y') (a : X ⟶ Y)
      [X.Over Z] [X.Over Z'] [X'.Over Z'] [Y.Over Z] [Y.Over Z'] [Y'.Over Z']
      [Z.Over Z'] [IsOverTower X Z Z'] [IsOverTower Y Z Z']
      [IsThickening (Z ↘ Z')] [IsFirstOrderThickening i] [IsFirstOrderThickening j]
      [i.IsOver Z'] [j.IsOver Z'] [a.IsOver Z] [a.IsOver Z']
      (hY : IsPullback (Y ↘ Z) j (Z ↘ Z') (Y' ↘ Z'))
      (sqX : CommSq (X ↘ Z) i (Z ↘ Z') (X' ↘ Z'))
      (A : (Modules.pullback a).obj (conormalSheaf j) ⟶ conormalSheaf i)
      (hA : baseConormalMap a hY.toCommSq ≫ A = Conormal.map sqX)
      (U' : X'.Opens) (s : sections Z' i j a A U'),
      Function.Bijective (fun theta : (parameterSheaf Z i a).1.obj (op U') ↦
        relativeBaseAct Z Z' i j a A U' theta s))

end AlgebraicGeometry.Scheme.Hom.Deformation
