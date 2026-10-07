module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber
public import stacks_project.Chap90.Remark_90_6_4

/-!
# Residue-slice of a category cofibered in groupoids

Slicing a category cofibered in groupoids over `ArtinianLocalAlgCat Λ k` at a
residue-fibre object `x` yields the predeformation category `F_x`. A based
morphism `φ` induces `φ_x : F_x ⟶ G_{φ(x)}`.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat Functor
open scoped Bicategory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F G : Type v} [Category.{w} F] [Category.{w} G]

namespace CategoryTheory.Functor

variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]

/-- The residue slice `F_x` of a category cofibered in groupoids `p` at a residue-fibre
object `x`, as the composite `Over.forget (Fiber.fiberInclusion.obj x) ⋙ p`. -/
abbrev sliceAt (x : p.Fiber (residue Λ k)) :
    Over (Fiber.fiberInclusion.obj x) ⥤ ArtinianLocalAlgCat Λ k :=
  Over.forget (Fiber.fiberInclusion.obj x) ⋙ p

/-- The residue slice is the forgetful functor of the over-category at `x`, composed with `p`. -/
theorem sliceAt_def (x : p.Fiber (residue Λ k)) :
    sliceAt p x = Over.forget (Fiber.fiberInclusion.obj x) ⋙ p := sorry

end CategoryTheory.Functor

namespace CategoryTheory.BasedFunctor

variable {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}
variable [IsFibered.InGroupoids p.op] [IsFibered.InGroupoids q.op]

/-- The residue-fibre object `φ(x)` obtained by applying the fibre functor of a based morphism
at `ArtinianLocalAlgCat.residue Λ k`. -/
abbrev objAt (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (x : p.Fiber (residue Λ k)) : q.Fiber (residue Λ k) :=
  (φ.fiberFunctor (residue Λ k)).obj x

/-- `objAt φ x` is the image of `x` under the fibre functor of `φ` at the residue field. -/
theorem objAt_def (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (x : p.Fiber (residue Λ k)) :
    objAt φ x = (φ.fiberFunctor (residue Λ k)).obj x := sorry

/-- A based morphism of categories cofibered in groupoids over `ArtinianLocalAlgCat Λ k`
commutes with residue slices after postcomposition on over-categories. -/
theorem sliceMap_w (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (x : p.Fiber (residue Λ k)) :
    Over.post φ.toFunctor ⋙ Functor.sliceAt q (objAt φ x) = Functor.sliceAt p x := sorry

/-- The induced based morphism `φ_x : F_x ⟶ G_{φ(x)}` on residue slices, given by
`Over.post` of the underlying functor. -/
def sliceMap (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (x : p.Fiber (residue Λ k)) :
    BasedCategory.ofFunctor (Functor.sliceAt p x) ⥤ᵇ
      BasedCategory.ofFunctor (Functor.sliceAt q (objAt φ x)) :=
  BasedFunctor.ofFunctor (Over.post φ.toFunctor) (sliceMap_w φ x)

/-- The underlying functor of `sliceMap φ x` is `Over.post φ.toFunctor`. -/
theorem sliceMap_toFunctor (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (x : p.Fiber (residue Λ k)) :
    (sliceMap φ x).toFunctor = Over.post φ.toFunctor := sorry

end CategoryTheory.BasedFunctor
