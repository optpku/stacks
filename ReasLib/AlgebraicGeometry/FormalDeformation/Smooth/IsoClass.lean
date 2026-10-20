module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth
public import ReasLib.CategoryTheory.Fibered.BasedCategory.ToIsoClass
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Elements

/-!
# Smoothness of the canonical fibre-class morphism

The canonical morphism from a category cofibered in groupoids over Artinian local algebras to
fibrewise isomorphism classes is smooth.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.BasedFunctor

/-- The canonical morphism to fibrewise isomorphism classes is smooth over Artinian local algebras. -/
instance instIsSmoothToIsoClass {F : Type w} [Category.{v} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op] :
    IsSmooth (toIsoClass p) := sorry

end CategoryTheory.BasedFunctor
