/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap38.«38_20_13_1_FlatFunctor»
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Flattening.Universal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable (ℱ : X.Modules) [ℱ.IsQuasicoherent]

/- Definition 38.21.1 (1): the universal flattening of `ℱ` exists when its flattening
functor on schemes over `S` is representable. -/
@[stacks 05P6] #check (AlgebraicGeometry.Scheme.Modules.HasUniversalFlattening :
  ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent], Prop)

/- Definition 38.21.1 (2): the universal flattening of `X` is the universal flattening
of its structure module `SheafOfModules.unit X.ringCatSheaf`. -/
@[stacks 05P6] #check (AlgebraicGeometry.Scheme.HasUniversalFlattening :
  ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S), Prop)
