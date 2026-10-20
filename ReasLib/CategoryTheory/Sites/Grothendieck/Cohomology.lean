module

public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise
public import ReasLib.CategoryTheory.Sites.Grothendieck.LowerShriek

/-!
# Objectwise cohomology and restriction to a fiber of a simplicial site
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]

/-- Objectwise cohomology over a fiber object agrees with cohomology on that fiber
after restricting the coefficient sheaf from the total site. -/
@[stacks 0DBZ]
theorem cohomologyOverObject_fiber_iso
    [HasSheafify (topology F J) AddCommGrpCat.{max w v}]
    [HasExt.{w} (Sheaf (topology F J) AddCommGrpCat.{max w v})]
    (n : SimplexCategory)
    [HasSheafify ((J (op n)).toGrothendieck) AddCommGrpCat.{max w v}]
    [HasExt.{w} (Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{max w v})]
    (U : F.obj (op n)) (G : Sheaf (topology F J) AddCommGrpCat.{max w v})
    (p : ℕ) :
    IsIsomorphic
      (Sheaf.cohomologyOverObject G ((ι F (op n)).obj U) p)
      (Sheaf.cohomologyOverObject
        ((fiberRestrict F J AddCommGrpCat.{max w v} n).obj G) U p) :=
  sorry

end CategoryTheory.Grothendieck
