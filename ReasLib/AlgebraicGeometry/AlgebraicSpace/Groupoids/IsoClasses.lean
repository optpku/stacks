module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Basic
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Fibers

/-!
# Isomorphism classes of fibers of an algebraic space

Fiberwise isomorphism classes of the discrete groupoid fibration of an algebraic
space map canonically to its universe-raised functor of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open FiberedCategoryOver

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Comparison from fiberwise isomorphism classes of an algebraic space to its
universe-raised functor of points, by Grothendieck fiber evaluation. -/
noncomputable def isoClassToPoints {S : Scheme.{u}} (Y : AlgebraicSpace S) :
    Functor.fiberIsoClassPresheaf Y.toGroupoids.p ⟶
      Y.functorOfPoints ⋙ uliftFunctor.{u + 1, u} where
  app U :=
    TypeCat.ofHom (fun x ↦
      ULift.up.{u + 1, u}
        (Sets.ofPresheaf.fiberToValue Y.functorOfPoints (unop U)
          ((Functor.id
            (((CategoryOfElements.π Y.functorOfPoints).leftOp).Fiber
              (unop U))).isoClassesToObj x)))
  naturality := sorry

/-- On a represented fiber class, `isoClassToPoints` is universe-lifted Grothendieck
fiber evaluation. -/
theorem isoClassToPoints_app_mk {S : Scheme.{u}} (Y : AlgebraicSpace S)
    (U : (Over S)ᵒᵖ) (x : Y.toGroupoids.p.Fiber (unop U)) :
    (isoClassToPoints Y).app U (Quotient.mk'' x) =
      ULift.up
        (Sets.ofPresheaf.fiberToValue Y.functorOfPoints
          (unop U) x) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
