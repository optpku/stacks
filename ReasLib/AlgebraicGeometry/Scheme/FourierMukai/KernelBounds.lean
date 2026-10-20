/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Tensor.Instances
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor.Bifunctor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpace.ModuleDerived
open RingedSpace.ModuleDerived.Tensor (functor)
open Scheme.ModuleDerived.ProjectionFormula (hasDerivedTensorBifunctor)

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

variable {k : Type u} [Field k]

/-- A derived module has cohomology only in `[-m, m] ∪ [-m-n, m-n]`. -/
def IsSupportedInIntervals
    {S : Scheme.{u}} (E : RingedSpace.ModuleDerived S.toRingedSpace)
    (m n : ℕ) : Prop :=
  ∀ i : ℤ,
    ¬ (((-(m : ℤ) ≤ i ∧ i ≤ (m : ℤ)) ∨
        (-(m : ℤ) - (n : ℤ) ≤ i ∧ i ≤ (m : ℤ) - (n : ℤ)))) →
      IsZero (cohomologySheaf E i)

/-- A derived module has no cohomology outside the central interval `[-m, m]`. -/
def IsSupportedInCentralInterval
    {S : Scheme.{u}} (E : RingedSpace.ModuleDerived S.toRingedSpace)
    (m : ℕ) : Prop :=
  ∀ i : ℤ, ¬ (-(m : ℤ) ≤ i ∧ i ≤ (m : ℤ)) →
    IsZero (cohomologySheaf E i)

/-- A derived module has no cohomology outside the shifted lower interval
`[-m-n, m-n]`. -/
def IsSupportedInLowerInterval
    {S : Scheme.{u}} (E : RingedSpace.ModuleDerived S.toRingedSpace)
    (m n : ℕ) : Prop :=
  ∀ i : ℤ, ¬ (-(m : ℤ) - (n : ℤ) ≤ i ∧ i ≤ (m : ℤ) - (n : ℤ)) →
    IsZero (cohomologySheaf E i)

/-- The two-variable Fourier--Mukai functor on the product of `X` with `X × Y`. -/
noncomputable def bifunctor
    (X Y : SchemeOverField k) :
    (RingedSpace.ModuleDerived X.left.toRingedSpace ×
        RingedSpace.ModuleDerived (pullback X.hom Y.hom).toRingedSpace) ⥤
      RingedSpace.ModuleDerived Y.left.toRingedSpace :=
  Functor.prod
      (RingedSpace.modulePullbackDerived
        (pullback.fst X.hom Y.hom).toLRSHom.toShHom)
        (𝟭 (RingedSpace.ModuleDerived (pullback X.hom Y.hom).toRingedSpace)) ⋙
    @functor (pullback X.hom Y.hom).toRingedSpace
      (hasDerivedTensorBifunctor (pullback X.hom Y.hom)) ⋙
    RingedSpace.moduleDerivedPushforward
      (pullback.snd X.hom Y.hom).toLRSHom.toShHom

/-- The Fourier--Mukai transform of a module `F` by a perfect kernel `E`. -/
noncomputable abbrev transform
    (X Y : SchemeOverField k) (F : X.left.Modules)
    (E : @RingedSpace.ModuleDerived.Perfect (pullback X.hom Y.hom).toRingedSpace) :
    RingedSpace.ModuleDerived Y.left.toRingedSpace :=
  (bifunctor X Y).obj
    ((DerivedCategory.singleFunctor X.left.toRingedSpace.Modules (0 : ℤ)).obj
      (Scheme.Modules.toRingedSpaceObj X.left F), E.obj)

/-- The transition map induced by a morphism of consecutive perfect kernels. -/
noncomputable abbrev transition
    (X Y : SchemeOverField k)
    (K : ℕ ⥤ @RingedSpace.ModuleDerived.Perfect (pullback X.hom Y.hom).toRingedSpace)
    (F : X.left.Modules) (n : ℕ) :
    transform X Y F (K.obj n) ⟶ transform X Y F (K.obj (n + 1)) :=
  (bifunctor X Y).map
    (Prod.mkHom (𝟙 _) ((K.map (homOfLE (Nat.le_succ n))).hom))

/-- For a system of perfect kernels on a product of finite-type schemes over a field,
two-interval bounds and eventual central cohomology isomorphisms for every coherent
zero-dimensional test module imply the same two-interval bounds for the kernels. -/
theorem kernel_amplitude
    (X Y : SchemeOverField k) (hX : Algebraic X) (hY : Algebraic Y) (m : ℕ)
    (K : ℕ ⥤ @RingedSpace.ModuleDerived.Perfect (pullback X.hom Y.hom).toRingedSpace)
    (hK : ∀ (n : ℕ) (q : ℤ), (m : ℤ) < q →
      IsZero (cohomologySheaf (K.obj n).obj q))
    (hF : ∀ (F : X.left.Modules), F.IsCoherent →
      topologicalKrullDim
          (RingedSpace.moduleSupport (Scheme.Modules.toRingedSpaceObj X.left F)) = 0 →
      (∀ n : ℕ, IsSupportedInIntervals (transform X Y F (K.obj n)) m n) ∧
        (∀ n : ℕ, 2 * m < n →
          ∀ i : ℤ, -(m : ℤ) ≤ i → i ≤ (m : ℤ) →
            IsIso (cohomologySheafMap (transition X Y K F n) i))) :
    ∀ n : ℕ, IsSupportedInIntervals (K.obj n).obj m n := sorry

/-- For a system of perfect kernels on a product of finite-type schemes over a field,
two-interval bounds and eventual central cohomology isomorphisms for every coherent
zero-dimensional test module imply central cohomology isomorphisms for the kernel transitions
once `n > 2m`. -/
theorem kernel_transition_isIso
    (X Y : SchemeOverField k) (hX : Algebraic X) (hY : Algebraic Y) (m : ℕ)
    (K : ℕ ⥤ @RingedSpace.ModuleDerived.Perfect (pullback X.hom Y.hom).toRingedSpace)
    (hK : ∀ (n : ℕ) (q : ℤ), (m : ℤ) < q →
      IsZero (cohomologySheaf (K.obj n).obj q))
    (hF : ∀ (F : X.left.Modules), F.IsCoherent →
      topologicalKrullDim
          (RingedSpace.moduleSupport (Scheme.Modules.toRingedSpaceObj X.left F)) = 0 →
      (∀ n : ℕ, IsSupportedInIntervals (transform X Y F (K.obj n)) m n) ∧
        (∀ n : ℕ, 2 * m < n →
          ∀ i : ℤ, -(m : ℤ) ≤ i → i ≤ (m : ℤ) →
            IsIso (cohomologySheafMap (transition X Y K F n) i))) :
    ∀ n : ℕ, 2 * m < n →
      ∀ i : ℤ, -(m : ℤ) ≤ i → i ≤ (m : ℤ) →
        IsIso (cohomologySheafMap ((K.map (homOfLE (Nat.le_succ n))).hom) i) := sorry

/-- A system of perfect kernels on a product of smooth finite-type schemes over a field
whose zero-dimensional coherent test transforms satisfy two-interval bounds and eventual
central cohomology isomorphisms eventually splits into a fixed central perfect object and
shifted lower perfect objects, compatibly with the transitions. -/
theorem eventually_split
    (X Y : SchemeOverField k) (hX : Algebraic X) (hY : Algebraic Y)
    [Smooth X.hom] [Smooth Y.hom] (m : ℕ)
    (K : ℕ ⥤ @RingedSpace.ModuleDerived.Perfect (pullback X.hom Y.hom).toRingedSpace)
    (hK : ∀ (n : ℕ) (q : ℤ), (m : ℤ) < q →
      IsZero (cohomologySheaf (K.obj n).obj q))
    (hF : ∀ (F : X.left.Modules), F.IsCoherent →
      topologicalKrullDim
          (RingedSpace.moduleSupport (Scheme.Modules.toRingedSpaceObj X.left F)) = 0 →
      (∀ n : ℕ, IsSupportedInIntervals (transform X Y F (K.obj n)) m n) ∧
        (∀ n : ℕ, 2 * m < n →
          ∀ i : ℤ, -(m : ℤ) ≤ i → i ≤ (m : ℤ) →
            IsIso (cohomologySheafMap (transition X Y K F n) i))) :
    ∃ (Klim : RingedSpace.ModuleDerived (pullback X.hom Y.hom).toRingedSpace),
      IsPerfect Klim ∧
      IsSupportedInCentralInterval Klim m ∧
      ∃ (N : ℕ)
        (C : ℕ → RingedSpace.ModuleDerived (pullback X.hom Y.hom).toRingedSpace),
        (∀ n : ℕ, N ≤ n →
          IsPerfect (C n) ∧
            IsSupportedInLowerInterval (C n) m n) ∧
        ∃ (e : ∀ n : ℕ, N ≤ n →
            ((K.obj n).obj ≅ (Klim ⊞ C n)))
          (c : ∀ n : ℕ, C n ⟶ C (n + 1))
          (u : ∀ n : ℕ, Klim ⟶ Klim),
          (∀ n : ℕ, IsIso (u n)) ∧
          ∀ (n : ℕ) (hn : N ≤ n),
            (e n hn).hom ≫ biprod.map (u n) (c n) =
              (K.map (homOfLE (Nat.le_succ n))).hom ≫
                (e (n + 1) (Nat.le_trans hn (Nat.le_succ n))).hom := sorry

end AlgebraicGeometry.Scheme.FourierMukai
