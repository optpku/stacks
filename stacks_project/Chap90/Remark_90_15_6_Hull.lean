module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Hull
import StacksCheckRecall

/-!
# Hulls of formal objects

A hull is a versal formal object whose differential is bijective. The reusable
definition is provided by the formal-deformation library.
-/

@[expose] public section

open CategoryTheory

universe u

/- Remark 90.15.6: a hull is a versal formal object whose differential is bijective. -/
@[stacks 06IY] #check (FormalObject.IsHull :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k]
    {F : Type (u + 1)} [Category.{u + 1} F]
    {p : F ⥤ ArtinianLocalAlgCat Λ k}
    (ξ : FormalObject p) [Functor.IsPredeformationCategory p], Prop)
