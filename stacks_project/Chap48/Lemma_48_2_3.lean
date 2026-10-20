/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.AffineComparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory.InternalHom
open CategoryTheory.MonoidalClosed
open Functor.PullbackInternalHom.Left
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.ModuleDerived
open Scheme
open Scheme.ModuleDerived.InternalHom

noncomputable section

universe u

/- Lemma 48.2.3: over a Noetherian commutative ring, affine tilde carries the derived Hom
of a complex with finite cohomology modules into a complex of finite injective dimension to
the derived internal Hom of the corresponding complexes on the affine spectrum. -/
@[stacks 0A88]
#check
  (AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.affineComparison_isIso_of_finiteCohomology_finiteInjectiveDimension :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [@RHom.Has.{u, u} A _]
      [KFlat.HomotopyTensorDescends (Spec (CommRingCat.of A)).toRingedSpace]
      [KFlat.TensorDescends (Spec (CommRingCat.of A)).toRingedSpace]
      [KFlat.IsLocalization (Spec (CommRingCat.of A)).toRingedSpace]
      (M : @RHom.BifunctorComparison A _ _ _)
      (H : MonoidalClosed
        (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace))
      (T : Functor.TensorComparison
        (AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.affineTildeDerived A))
      (K L : DerivedCategory (ModuleCat.{u} A)),
      (∀ i : ℤ,
        Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) →
      DerivedCategory.HasFiniteInjectiveDimension L →
      IsIso
        (AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.affineComparison M H T K L))
