/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Elements
public import stacks_project.Chap90.Definition_90_27_1_MinimalVersal
public import stacks_project.Chap90.Remark_90_6_3
public import stacks_project.Chap90.Remark_90_10_3
public import stacks_project.Chap90.Remark_90_13_5_SchlessingerH3
import StacksCheckRecall

/-!
# Schlessinger (H3) and versal formal objects of predeformation functors

For a predeformation functor satisfying (S1) and (S2), finite-dimensionality of
the tangent space is Schlessinger's (H3). Combined with (H1) and (H2), this
yields a versal formal object of the associated cofibered set.
-/

@[expose] public section

open CategoryTheory
open Functor.IsPredeformationFunctor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- Hom-universe lift of the category of elements of `F`, matching the object/hom
constraint of `FormalObject.IsVersal`. -/
abbrev elementsTotal (F : ArtinianLocalAlgCat Λ k ⥤ Type u) : Type (u + 1) :=
  ULiftHom.{u + 1} F.Elements

/-- `elementsTotal F` is the Hom-universe lift of `F.Elements`. -/
theorem elementsTotal_eq (F : ArtinianLocalAlgCat Λ k ⥤ Type u) :
    elementsTotal F = ULiftHom.{u + 1} F.Elements := sorry

/-- Projection of the Hom-universe lift of `F.Elements` to `ArtinianLocalAlgCat Λ k`. -/
def elementsProjection (F : ArtinianLocalAlgCat Λ k ⥤ Type u) :
    elementsTotal F ⥤ ArtinianLocalAlgCat Λ k :=
  (ULiftHom.down : elementsTotal F ⥤ F.Elements) ⋙ CategoryOfElements.π F

/-- `elementsProjection F` is `CategoryOfElements.π F` after Hom-universe forgetful. -/
theorem elementsProjection_eq (F : ArtinianLocalAlgCat Λ k ⥤ Type u) :
    elementsProjection F =
      (ULiftHom.down : elementsTotal F ⥤ F.Elements) ⋙ CategoryOfElements.π F := sorry

/-- The cofibered set associated to a predeformation functor is a predeformation
category. -/
instance instIsPredeformationCategory_pi
    {F : ArtinianLocalAlgCat Λ k ⥤ Type v} [IsPredeformationFunctor F] :
    IsPredeformationCategory (CategoryOfElements.π F) := sorry

/-- The Hom-universe lift of the cofibered set of a predeformation functor is a
predeformation category. -/
instance instIsPredeformationCategory_elementsProjection
    {F : ArtinianLocalAlgCat Λ k ⥤ Type u} [IsPredeformationFunctor F] :
    IsPredeformationCategory (elementsProjection F) := sorry

end CategoryTheory.Functor

/- Remark 90.13.5 (1): for a predeformation functor `F : ArtinianLocalAlgCat Λ k ⥤ Type v`
satisfying (S1) and (S2), finite-dimensionality of `tangentSpace F` over `k` is
Schlessinger's (H3). Conditions (S1) and (S2) are `HasSchlessingerH1` and
`HasSchlessingerH2` by Remark 90.10.3. -/
@[stacks 0D3G] #check Functor.HasSchlessingerH3

namespace CategoryTheory.Functor

/-- Remark 90.13.5 (2): if `F` is a predeformation functor satisfying Schlessinger's
(H1), (H2), and (H3), then `elementsProjection F`, the Hom-universe lift
`ULiftHom.down ⋙ CategoryOfElements.π F` required by `FormalObject.IsVersal`,
admits a versal formal object. Conditions (S1) and (S2) are `HasSchlessingerH1` and
`HasSchlessingerH2` by Remark 90.10.3. -/
@[stacks 0D3G]
theorem exists_isVersal_pi (F : ArtinianLocalAlgCat Λ k ⥤ Type u)
    [IsPredeformationFunctor F] [HasSchlessingerH1 F] [HasSchlessingerH2 F]
    [AddCommGroup (tangentSpace F)] [Module k (tangentSpace F)]
    [HasSchlessingerH3 F] :
    ∃ ξ : FormalObject (elementsProjection F), FormalObject.IsVersal ξ := sorry

end CategoryTheory.Functor
