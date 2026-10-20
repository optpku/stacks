/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.FrobeniusStalk
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.Scheme.Etale AlgebraicGeometry.SchemeOverField

universe u v w

/- Definition 64.3.10: if `x : 𝟙_ ⟶ X` is a `k`-rational point of a scheme `X`
over a finite field `k`, and `x̄ : Spec(AlgebraicClosure k) ⟶ X` is the
geometric point lying over `x`, the geometric Frobenius
`π_x : F_x̄ ⟶ F_x̄` is the action of `frob_k⁻¹` on the étale stalk.
Here `x̄` is `homSpecGeometric` / `geometricPointOfHomSpec`, and `π_x` is
`geometricFrobeniusStalkHom`, the action of `(FiniteField.arithmeticFrobenius k)⁻¹`.
Taking `A = AddCommGrpCat` gives the source's arbitrary abelian sheaf;
the existing module construction `geometricFrobeniusStalk` is a specialization.
This notation is not standard; SGA4.5 writes `F_x`. -/
@[stacks 03SW] #check (AlgebraicGeometry.Scheme.Etale.geometricFrobeniusStalkHom :
  ∀ {k : Type u} [Field k] [Fintype k] {A : Type v} [Category.{w} A]
    [CategoryTheory.Limits.HasColimitsOfSize.{u, u} A] {X : SchemeOverField k}
    (F : Sheaf X.left.smallEtaleTopology A) (x : 𝟙_ (SchemeOverField k) ⟶ X),
    (Scheme.pointSmallEtale (homSpecGeometric x)).presheafFiber.obj F.1 ⟶
      (Scheme.pointSmallEtale (homSpecGeometric x)).presheafFiber.obj F.1)

#check (AlgebraicGeometry.Scheme.Etale.geometricFrobeniusStalk_apply :
  ∀ {k : Type u} [Field k] {ℓ n : ℕ} [Fintype k] {X : SchemeOverField k}
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n))))
    (x : 𝟙_ (SchemeOverField k) ⟶ X)
    [CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u} (ZMod (ℓ ^ n))))]
    (m : geometricModuleStalk F (homSpecGeometric x)),
    geometricFrobeniusStalk F x m =
      let s := homSpecGeometric x
      let σiso := geometricPointGaloisIso x (FiniteField.arithmeticFrobenius k)⁻¹
      let Ftype := F.1 ⋙ CategoryTheory.forget (ModuleCat.{u} (ZMod (ℓ ^ n)))
      let e := geometricStalkForgetIso F s
      e.hom (stalkGaloisAction s σiso Ftype (e.inv m)))

#check (AlgebraicGeometry.SchemeOverField.homSpecGeometric :
  ∀ {k : Type u} [Field k] {X : SchemeOverField k}
    (x : 𝟙_ (SchemeOverField k) ⟶ X),
    Spec (CommRingCat.of (AlgebraicClosure k)) ⟶ X.left)

#check (AlgebraicGeometry.SchemeOverField.geometricPointOfHomSpec :
  ∀ {k : Type u} [Field k] {X : SchemeOverField k}
    (x : 𝟙_ (SchemeOverField k) ⟶ X), Scheme.GeometricPoint X.left)

#check (AlgebraicGeometry.SchemeOverField.geometricPointOfHomSpec_image :
  ∀ {k : Type u} [Field k] {X : SchemeOverField k}
    (x : 𝟙_ (SchemeOverField k) ⟶ X),
    (geometricPointOfHomSpec x).image = x.left (IsLocalRing.closedPoint k))
