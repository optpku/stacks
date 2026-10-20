/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Flattening.Stratification
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 38.21.3 (1): a quasicoherent module has a flattening stratification when its
flattening functor is represented by a monomorphism associated to a stratification of the base
by locally closed subschemes. -/
@[stacks 05P7] #check
  (@AlgebraicGeometry.Scheme.Modules.Flattening.hasStratification_iff.{u} :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)
        [ℱ.IsQuasicoherent],
      AlgebraicGeometry.Scheme.Modules.Flattening.HasStratification f ℱ ↔
        ∃ S' : Over S,
          Nonempty
              ((AlgebraicGeometry.Scheme.Modules.Flattening.functor f ℱ).RepresentableBy S') ∧
            S'.hom.IsStratification)

/- Definition 38.21.3 (2): a scheme has a flattening stratification when its structure module
has a flattening stratification relative to the given morphism. -/
@[stacks 05P7] #check
  (@AlgebraicGeometry.Scheme.Flattening.hasStratification_iff.{u} :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.Scheme.Flattening.HasStratification f ↔
        @AlgebraicGeometry.Scheme.Modules.Flattening.HasStratification X S f
          (AlgebraicGeometry.Scheme.AssociatedModule.structureModule X).obj
          (AlgebraicGeometry.Scheme.AssociatedModule.structureModule X).property)
