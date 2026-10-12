/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace

/-!
# Tangent space of a predeformation category

The tangent space `T F` of a predeformation category `p : F ⥤ ArtinianLocalAlgCat Λ k` is the
type of isomorphism classes of objects in the fibre of `p` over the dual numbers.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsPredeformationCategory p]

#check (Functor.tangentSpace p : Type v)
#check (Functor.tangentSpace_def p :
  Functor.tangentSpace p =
    isomorphismClasses.obj (Cat.of (p.Fiber (ArtinianLocalAlgCat.dualNumber Λ k))))
#check (Functor.tangentSpace.mk p :
  p.Fiber (ArtinianLocalAlgCat.dualNumber Λ k) → Functor.tangentSpace p)
#check (Functor.tangentSpace.mk_eq_mk p :
  ∀ fiberObject otherObject : p.Fiber (ArtinianLocalAlgCat.dualNumber Λ k),
    Functor.tangentSpace.mk p fiberObject = Functor.tangentSpace.mk p otherObject ↔
      Nonempty (fiberObject ≅ otherObject))
