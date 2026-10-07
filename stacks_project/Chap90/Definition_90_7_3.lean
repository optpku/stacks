module

public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal
public import stacks_project.Chap90.Definition_90_7_3_CompleteLocal
public import stacks_project.Chap90.Definition_90_7_3_FormalObject

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

/-- Definition 90.7.3: if `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids,
the functor `completion p : FormalObject p ⥤ CompleteLocalAlgCat Λ k` sending a formal
object `(R, ξ_n, f_n)` to `R` is the completion of `F`. -/
@[stacks 06H5]
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
