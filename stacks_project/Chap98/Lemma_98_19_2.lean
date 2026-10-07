module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap98.Definition_98_11_1_LimitPreserving
public import stacks_project.Chap98.Definition_98_13_1_Versal
public import stacks_project.Chap98.Definition_98_18_1
import Mathlib.Tactic.CrossRefAttribute

/-!
# Generalization of versality along specializations of finite type points

On a locally Noetherian base, if a category fibred in groupoids over
`(Sch/S)_fppf` has representable-by-algebraic-spaces diagonal, (RS*), and is
limit preserving, then versality of an object over a finite-type scheme
persists along specializations of finite type points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Lemma 98.19.2: let `S` be a locally Noetherian scheme and let `X` be a
category fibred in groupoids over `(Sch/S)_fppf`. Assume the diagonal
`Δ : X ⟶ X × X` is representable by algebraic spaces, `X` has (RS*), and
`X` is limit preserving. Let `x` be an object of `X` over a scheme `U` of
finite type over `S`, and let `u ⤳ u0` be a specialization of finite type
points of `U` such that `x` is versal at `u0`. Then `x` is versal at `u`. -/
@[stacks 0G2K]
theorem isVersalAt_of_specializes {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    [Groupoids.LimitPreserving X]
    (h_diag : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
    {U : Scheme.{u}} (hU : U ⟶ S) [Scheme.Hom.FiniteType hU]
    (x : X.total) (hx : X.p.obj x = Over.mk hU) {u u0 : U}
    [IsFiniteTypePoint u] [IsFiniteTypePoint u0]
    (h_specializes : Specializes u u0) (h_versal : IsVersalAt hU x hx u0) :
    IsVersalAt hU x hx u :=
  sorry

end AlgebraicGeometry.GroupoidsOver
