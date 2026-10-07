module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Opposites
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Basic
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal

/-!
# Associated functor of isomorphism classes

The covariant functor sending an object `A` of `ArtinianLocalAlgCat Λ k` to the type of
isomorphism classes in the fibre of a cofibered groupoid `p` over `A`.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- The covariant functor of fibrewise isomorphism classes associated to a category cofibered
in groupoids `p : F ⥤ ArtinianLocalAlgCat Λ k`. -/
noncomputable def isoClassFunctor (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] : ArtinianLocalAlgCat Λ k ⥤ Type v :=
  opOp (ArtinianLocalAlgCat Λ k) ⋙ fiberIsoClassPresheaf p.op

/-- The value of `isoClassFunctor p` at `A` is the type of isomorphism classes in the fibre of
`p.op` over `op A`. -/
theorem isoClassFunctor_obj (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] (A : ArtinianLocalAlgCat Λ k) :
    (isoClassFunctor p).obj A =
      isomorphismClasses.obj (Cat.of ((p.op).Fiber (op A))) := sorry

/-- Restriction of a represented fibrewise isomorphism class along `f` may be computed using any
cleavage of `p.op`. -/
theorem isoClassFunctor_map_mk (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] (χ : (p.op).Cleavage)
    {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) (x : (p.op).Fiber (op A)) :
    (isoClassFunctor p).map f (Quotient.mk'' x) = Quotient.mk'' ((f.op)⁎[χ] x) := sorry

/-- The category of elements of `isoClassFunctor p` is cofibered in groupoids over
`ArtinianLocalAlgCat Λ k`. -/
instance isoClassFunctor_op_isFiberedInGroupoids (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] :
    IsFibered.InGroupoids (CategoryOfElements.π (isoClassFunctor p)).op := sorry

end CategoryTheory.Functor
