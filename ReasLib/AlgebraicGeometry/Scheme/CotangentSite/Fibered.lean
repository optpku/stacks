/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CotangentSite.Site
public import Mathlib.CategoryTheory.FiberedCategory.Fibered

/-!
# Restriction of polynomial-affine diagrams

Composition on the open-subscheme side gives strongly cartesian lifts for
the projection to the small Zariski site.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CotangentSite

variable {Λ : CommRingCat.{u}} {X : Scheme.{u}} [X.Over (Spec Λ)]

/-- Restriction of `U ⟶ A` along `U' ⟶ U` keeps the polynomial affine target
fixed and composes the diagram map with the given map of open subschemes. -/
def restrict (diagram : category Λ X) {domain : X.smallZariskiSite}
    (baseMap : domain ⟶ (forgetZariski Λ X).obj diagram) : category Λ X where
  left := domain
  right := diagram.right
  hom := Over.homMk (baseMap.left ≫ diagram.hom.left) sorry

/-- The comparison from a restricted diagram has the given map of open
subschemes as its left component and the identity as its target component. -/
def restrictHom (diagram : category Λ X) {domain : X.smallZariskiSite}
    (baseMap : domain ⟶ (forgetZariski Λ X).obj diagram) :
    restrict diagram baseMap ⟶ diagram where
  left := baseMap
  right := 𝟙 diagram.right
  w := sorry

/-- Restriction comparison morphisms are strongly cartesian over the chosen
map in the small Zariski site. -/
instance restrictHom_isStronglyCartesian (diagram : category Λ X)
    {domain : X.smallZariskiSite} (baseMap : domain ⟶ (forgetZariski Λ X).obj diagram) :
    (forgetZariski Λ X).IsStronglyCartesian baseMap (restrictHom diagram baseMap) := sorry

/-- The category of polynomial-affine diagrams over a scheme is fibered over
its small Zariski site via the projection to the open subscheme. -/
instance forgetZariski_isFibered (Λ : CommRingCat.{u}) (X : Scheme.{u})
    [X.Over (Spec Λ)] : (forgetZariski Λ X).IsFibered := sorry

end AlgebraicGeometry.Scheme.CotangentSite
