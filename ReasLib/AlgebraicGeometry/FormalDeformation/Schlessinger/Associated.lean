/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.Combinatorics.Quiver.Basic
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Basic
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.Automorphisms

/-!
# Associated functors and Schlessinger's conditions

The covariant functor of fibrewise isomorphism classes inherits Schlessinger's conditions
from a category cofibered in groupoids, with a residue-fibre hypothesis for (S2).
-/

@[expose] public section

open CategoryTheory Opposite ArtinianLocalAlgCat

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

/-- If a category cofibered in groupoids over Artinian local algebras satisfies (S1),
then its associated functor of isomorphism classes satisfies (S1). -/
theorem hasSchlessingerS1_isoClass (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] [HasSchlessingerS1 p] :
    HasSchlessingerS1 (CategoryOfElements.π (isoClassFunctor p)) := sorry

/-- A category cofibered in groupoids satisfying (S2) passes (S2) to its associated functor
when it is a predeformation category, its residue fibre is discrete or thin, or every
automorphism pushforward along a lift of `k[ε] ⟶ k` is surjective. -/
theorem hasSchlessingerS2_isoClass (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] [HasSchlessingerS2 p]
    (h : IsPredeformationCategory p ∨
      IsDiscrete (p.Fiber (residue Λ k)) ∨
      Quiver.IsThin (p.Fiber (residue Λ k)) ∨
      ∀ {xε x0 : F} (φ : xε ⟶ x0) [p.IsHomLift (dualNumberToResidue Λ k) φ],
        Function.Surjective (autPushforward p φ)) :
    HasSchlessingerS2 (CategoryOfElements.π (isoClassFunctor p)) := sorry

end CategoryTheory.Functor
