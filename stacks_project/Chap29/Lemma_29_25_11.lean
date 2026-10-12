/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Open
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Lemma 29.25.11: let `f : X ⟶ Y` be a morphism of schemes and let `ℱ` be a
quasi-coherent `𝒪_X`-module. If `f` is locally of finite presentation, `ℱ` is of finite type,
`moduleSupport ℱ = Set.univ`, and `ℱ` is flat over `Y`, then `f` is universally open. -/
@[stacks 0CVT] #check
  (AlgebraicGeometry.Scheme.Modules.universallyOpen_of_flatOver_of_moduleSupport_eq_univ :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (ℱ : X.Modules)
      [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] [LocallyOfFinitePresentation f],
      AlgebraicGeometry.Scheme.Modules.moduleSupport ℱ = Set.univ →
        AlgebraicGeometry.Scheme.Modules.flatOver ℱ f → UniversallyOpen f)
