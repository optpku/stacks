/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject

/-!
# Completion of a category cofibered in groupoids over `C_Λ`

The completion of `p : F ⥤ ArtinianLocalAlgCat Λ k` is the functor from formal
objects of `p` to `CompleteLocalAlgCat Λ k` sending a formal object to its
complete local base.
-/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

namespace CategoryTheory.Functor

/-- The completion functor sends each formal object to its complete local base. -/
noncomputable def completion (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] :
    FormalObject p ⥤ CompleteLocalAlgCat Λ k where
  obj ξ := ξ.base
  map a := a.base
  map_id := sorry
  map_comp := sorry

/-- The completion sends a formal object to its complete local base. -/
theorem completion_obj (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (ξ : FormalObject p) :
    (completion p).obj ξ = ξ.base := sorry

/-- The completion sends a morphism of formal objects to its complete local base map. -/
theorem completion_map (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    {ξ η : FormalObject p} (a : ξ ⟶ η) :
    (completion p).map a = a.base := sorry

/-- The completion of a category cofibered in groupoids is again cofibered in groupoids. -/
instance completion_op_isFiberedInGroupoids (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] :
    IsFibered.InGroupoids (completion p).op := sorry

end CategoryTheory.Functor
