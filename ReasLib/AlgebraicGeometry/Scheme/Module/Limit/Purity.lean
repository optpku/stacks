/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity
public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Over

/-!
# Purity of modules over inverse limits of schemes

Purity and flatness along a selected fibre of a finitely presented module descend together with
the finitely presented scheme and module to a stage of a directed inverse system of affine schemes.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules
namespace IsPureAlong

/-- A finitely presented scheme and finitely presented quasicoherent module over a directed inverse
limit of affine schemes descend to one stage while remaining pure and flat along the fibre over the
projected point. -/
theorem exists_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsAffine (D.obj i)]
    (X : Over c.pt) [Scheme.Hom.FinitePresentation X.hom]
    (ℱ : X.left.Modules) [ℱ.IsFinitePresentation] (s : c.pt)
    (h_pure : ℱ.IsPureAlong X.hom s)
    (h_flat : ∀ x : X.hom.fiber s, flatOverAt ℱ X.hom (X.hom.fiberι s x)) :
    ∃ (i : I) (Xi : FinitePresentationOver (D.obj i))
      (ℱi : FinitePresentationModules Xi.obj.left) (g : X.left ⟶ Xi.obj.left),
      IsPullback g X.hom Xi.obj.hom (c.π.app i) ∧
        ℱi.obj.IsPureAlong Xi.obj.hom ((c.π.app i) s) ∧
        (∀ x : Scheme.Hom.fiber Xi.obj.hom ((c.π.app i) s),
          flatOverAt ℱi.obj Xi.obj.hom
            (Scheme.Hom.fiberι Xi.obj.hom ((c.π.app i) s) x)) ∧
        Nonempty ((Scheme.Modules.pullback g).obj ℱi.obj ≅ ℱ) := sorry

end IsPureAlong
end AlgebraicGeometry.Scheme.Modules
