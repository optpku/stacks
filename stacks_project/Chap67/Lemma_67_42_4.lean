/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat.Valuation
import StacksCheckRecall

/-!
# Lifting valuation rings through flat morphisms of algebraic spaces

A flat morphism of algebraic spaces lifts a valuation-ring point of the target after an
extension of valuation rings, provided the closed point of the source spectrum lands in the
image of the map on points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.42.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a flat morphism of algebraic
spaces over `S`. Let `Spec(A) ⟶ Y` be a morphism where `A` is a valuation ring. If the
closed point of `Spec(A)` maps to a point of `|Y|` in the image of `|X| ⟶ |Y|`, then there
exists a commutative square `Spec(A') ⟶ X` over `Spec(A) ⟶ Y` where `A → A'` is an
extension of valuation rings in the sense of `IsExtensionOfValuationRings`. -/
@[stacks 089F] #check
  (AlgebraicGeometry.AlgebraicSpace.Flat.exists_isExtensionOfValuationRings :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [Flat f] {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    (σ : Spec (.of A) ⟶ S) (g : ofOver (Over.mk σ) ⟶ Y)
    (h_image : Points.map g (ofOver.pointsEquiv (Over.mk σ) (IsLocalRing.closedPoint A)) ∈
      Set.range (Points.map f)),
    ∃ (A' : Type u) (_ : CommRing A') (_ : IsDomain A') (_ : ValuationRing A')
      (_ : Algebra A A') (_ : IsExtensionOfValuationRings A A')
      (lift : ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A A')) ≫ σ)) ⟶ X),
      CommSq lift (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A A'))) rfl) f g)

end AlgebraicGeometry.AlgebraicSpace
