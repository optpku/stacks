module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.HigherDirectImage
import StacksCheckRecall

/-!
With the assumptions and notation of Lemma 103.15.1, the higher direct image
`R^p f'_* H` of an abelian sheaf on the lisse-étale (resp. flat-fppf) site is
the sheaf associated to the primed cohomology presheaf
`y ↦ H^p((V ×_{y, Y} X)', (pr')⁻¹ H)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.GroupoidsOver CategoryTheory CategoryTheory.Abelian
open scoped Bicategory

universe u

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]
variable (f : X ⟶ Y)

section Smooth

variable [Smooth f]
variable [HasSheafify (lisseEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (lisseEtaleTopology Y) AddCommGrpCat.{u + 1}]
variable [HasInjectiveResolutions (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1})]
variable (H : Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1}) (p : ℕ)

/- Lemma 103.15.2 (1): if `H` is an abelian sheaf on `X_lisse,étale`, then
`R^p f'_* H` is the sheaf associated to `y ↦ H^p((V ×_{y, Y} X)', (pr')⁻¹ H)`. -/
@[stacks 0GR2]
#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleHigherDirectImageIso f H p :
  lisseEtaleHigherDirectImage f H p ≅
    (presheafToSheaf (lisseEtaleTopology Y) AddCommGrpCat.{u + 1}).obj
      (lisseEtaleHigherDirectImagePresheaf f H p))

end Smooth

section Flat

variable [Flat f]
variable [HasSheafify (flatFppfTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (flatFppfTopology Y) AddCommGrpCat.{u + 1}]
variable [HasInjectiveResolutions (Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1})]
variable (H : Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1}) (p : ℕ)

/- Lemma 103.15.2 (2): if `H` is an abelian sheaf on `X_flat,fppf`, then
`R^p f'_* H` is the sheaf associated to `y ↦ H^p((V ×_{y, Y} X)', (pr')⁻¹ H)`. -/
@[stacks 0GR2]
#check (AlgebraicGeometry.AlgebraicStack.flatFppfHigherDirectImageIso f H p :
  flatFppfHigherDirectImage f H p ≅
    (presheafToSheaf (flatFppfTopology Y) AddCommGrpCat.{u + 1}).obj
      (flatFppfHigherDirectImagePresheaf f H p))

end Flat
