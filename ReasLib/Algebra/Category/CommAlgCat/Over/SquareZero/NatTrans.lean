module

public import ReasLib.Algebra.Category.CommAlgCat.Over.SquareZero.Evaluation
public import ReasLib.Algebra.Category.ModuleCat.LinearLift.NatTrans

/-!
# Natural transformations on square-zero evaluations

Natural transformations between functors with singleton evaluation at the base
ring and bijective square-zero product comparisons act linearly on the canonical
module structures of their square-zero evaluations.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open TrivSqZeroExt

universe u

namespace CategoryTheory.Functor

variable {S R : Type u} [CommRing S] [CommRing R] [Algebra S R]
variable {P : ObjectProperty (Over (CommAlgCat.of S R))}
variable [P.IsClosedUnderIsomorphisms] [P.ContainsFGTrivSqZeroExt]
variable {F G : P.FullSubcategory ⥤ Type u}
variable [Unique (F.obj (overSelfObj P))] [F.BijectiveOnFGSquareZeroProds]
variable [Unique (G.obj (overSelfObj P))] [G.BijectiveOnFGSquareZeroProds]

/-- A natural transformation between functors with singleton evaluation at the
base ring and bijective square-zero product comparisons is `R`-linear on the
evaluation at `R[M]` for every finitely generated `R`-module `M`, with the
canonical module structures on those evaluations. -/
theorem isLinearMap_app_fgLift (t : F ⟶ G) (M : FGModuleCat.{u} R) :
    IsLinearMap R (M := (fgEval P F).obj M) (M₂ := (fgEval P G).obj M)
      (t.app ((fgLift P).obj M) : (fgEval P F).obj M → (fgEval P G).obj M) :=
  sorry

/-- A natural transformation between functors with singleton evaluation at the
base ring and bijective square-zero product comparisons is `R`-linear on the
evaluation at the dual numbers `R[ε] = R[R]`, with the canonical module
structures on those evaluations. -/
theorem isLinearMap_app_fgLift_self (t : F ⟶ G) :
    IsLinearMap R
      (M := (fgEval P F).obj (FGModuleCat.of R R))
      (M₂ := (fgEval P G).obj (FGModuleCat.of R R))
      (t.app ((fgLift P).obj (FGModuleCat.of R R)) :
        (fgEval P F).obj (FGModuleCat.of R R) →
          (fgEval P G).obj (FGModuleCat.of R R)) :=
  sorry

end CategoryTheory.Functor
