/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Limit.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Diagram
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Factorization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.FiniteType

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FiniteTypeApproximationDiagram

/-- A quasi-separated finite-type morphism to the limit of a directed inverse system of
Noetherian schemes with affine transition morphisms admits a finite-type approximation at
some stage whose induced morphism to the corresponding pullback is a closed immersion. -/
theorem exists_closedImmersion_of_finiteType
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    {X : Scheme.{u}} (f : X ⟶ c.pt) [QuasiSeparated f] [Scheme.Hom.FiniteType f] :
    ∃ (i : I) (diagram : FiniteTypeApproximationDiagram f (c.π.app i)),
      Scheme.Hom.FiniteType diagram.toSi ∧
        IsClosedImmersion (pullback.lift f diagram.toW diagram.w.symm) := sorry

end AlgebraicGeometry.FiniteTypeApproximationDiagram
