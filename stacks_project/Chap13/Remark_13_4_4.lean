module

import ReasLib.CategoryTheory.Pretriangulated.Triangle.Special
import StacksCheckRecall

@[expose] public section

/-!
# Remark 13.4.4

The reusable owner is the neutral special-triangle API.  Covariant Hom
exactness is represented by `Triangle.IsSpecial`; the contravariant statement
is its canonical opposite-category view `Triangle.IsCoSpecial`.
-/

/- Remark 13.4.4 (1): special triangles have all shifted covariant Hom
exactness pairs. -/
@[stacks 09WA] #check @CategoryTheory.Pretriangulated.Triangle.IsSpecial

/- Remark 13.4.4 (2): co-special triangles are the opposite-category special
triangles. -/
@[stacks 09WA] #check @CategoryTheory.Pretriangulated.Triangle.IsCoSpecial

#check @CategoryTheory.Pretriangulated.Triangle.IsSpecial.coyoneda_exact₂
#check @CategoryTheory.Pretriangulated.Triangle.IsSpecial.coyoneda_exact₃
#check @CategoryTheory.Pretriangulated.Triangle.IsSpecial.coyoneda_exact₁
#check @CategoryTheory.Pretriangulated.Triangle.IsCoSpecial.yoneda_exact₂
#check @CategoryTheory.Pretriangulated.Triangle.IsCoSpecial.yoneda_exact₃
#check @CategoryTheory.Pretriangulated.Triangle.IsCoSpecial.yoneda_exact₁
#check @CategoryTheory.Pretriangulated.Triangle.IsSpecial.ofIso
#check @CategoryTheory.Pretriangulated.Triangle.IsCoSpecial.ofIso
#check @CategoryTheory.Pretriangulated.Triangle.IsSpecial.shift
#check @CategoryTheory.Pretriangulated.Triangle.IsSpecial.rotate
#check @CategoryTheory.Pretriangulated.Triangle.IsSpecial.invRotate

/- Remark 13.4.4 (3): the outer-isomorphism criterion for special triangles. -/
@[stacks 09WA] #check
  @CategoryTheory.Pretriangulated.Triangle.isIso₂_of_isIso₁₃_of_isSpecial

/- Remark 13.4.4 (4): the first-two-isomorphisms criterion for special triangles. -/
@[stacks 09WA] #check
  @CategoryTheory.Pretriangulated.Triangle.isIso₃_of_isIso₁₂_of_isSpecial

/- Remark 13.4.4 (5): the last-two-isomorphisms criterion for special triangles. -/
@[stacks 09WA] #check
  @CategoryTheory.Pretriangulated.Triangle.isIso₁_of_isIso₂₃_of_isSpecial

/- Remark 13.4.4 (6): the outer-isomorphism criterion for co-special triangles. -/
@[stacks 09WA] #check
  @CategoryTheory.Pretriangulated.Triangle.isIso₂_of_isIso₁₃_of_isCoSpecial

/- Remark 13.4.4 (7): the first-two-isomorphisms criterion for co-special triangles. -/
@[stacks 09WA] #check
  @CategoryTheory.Pretriangulated.Triangle.isIso₃_of_isIso₁₂_of_isCoSpecial

/- Remark 13.4.4 (8): the last-two-isomorphisms criterion for co-special triangles. -/
@[stacks 09WA] #check
  @CategoryTheory.Pretriangulated.Triangle.isIso₁_of_isIso₂₃_of_isCoSpecial

/- Remark 13.4.4 (9): distinguished triangles are special. -/
@[stacks 09WA] #check
  @CategoryTheory.Pretriangulated.Triangle.isSpecial_of_distinguished

/- Remark 13.4.4 (10): distinguished triangles are co-special. -/
@[stacks 09WA] #check
  @CategoryTheory.Pretriangulated.Triangle.isCoSpecial_of_distinguished

end
