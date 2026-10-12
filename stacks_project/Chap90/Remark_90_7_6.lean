/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.TypesCompletion
import StacksCheckRecall

/-!
# Set-valued completion of a functor on `C_Λ`

Identifying functors with cofibered sets, the completion of a functor
`F : ArtinianLocalAlgCat Λ k ⥤ Type w` is `Functor.typesCompletion F`.
-/

@[expose] public section

open CategoryTheory

universe u w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Remark 90.7.6: identifying functors with cofibered sets, the completion of
`F : ArtinianLocalAlgCat Λ k ⥤ Type w` is the functor
`Functor.typesCompletion F : CompleteLocalAlgCat Λ k ⥤ Type w` given by
`(typesCompletion F).obj S = limit (S.truncationSystem ⋙ F)`, matching
`hat{F}(S) = lim F(S ⧸ m_S^n)`. This agrees with the definition in
Schlessinger's paper. -/
@[stacks 06H8] #check
  (CategoryTheory.Functor.typesCompletion :
    (ArtinianLocalAlgCat Λ k ⥤ Type w) → (CompleteLocalAlgCat Λ k ⥤ Type w))
