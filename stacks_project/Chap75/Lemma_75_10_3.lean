/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap75.Definition_75_9_1_Square
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.MayerVietoris.RelativePushforward
import StacksCheckRecall

/-! Relative Mayer–Vietoris triangle for derived pushforward. -/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Pretriangulated
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 75.10.3 -/
@[stacks 08JK]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.mayerVietorisRelativePushforward_mem_distTriang :
  ∀ {S : Scheme.{u}} {U V X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (j : U ⟶ X) [Etale j] (g : V ⟶ X) [Etale g]
    [IsElementaryDistinguishedSquare j g] (E : ModuleDerived X),
    mayerVietorisRelativePushforwardTriangle f j g E ∈ distTriang (ModuleDerived Y))

/- The triangle is functorial in the derived module. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.mayerVietorisRelativePushforwardTriangleFunctor :
  ∀ {S : Scheme.{u}} {U V X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (j : U ⟶ X) [Etale j] (g : V ⟶ X) [Etale g]
    [IsElementaryDistinguishedSquare j g],
    ModuleDerived X ⥤ Triangle (ModuleDerived Y))

/- Evaluation of the triangle functor. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.mayerVietorisRelativePushforwardTriangleFunctor_obj :
  ∀ {S : Scheme.{u}} {U V X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (j : U ⟶ X) [Etale j] (g : V ⟶ X) [Etale g]
    [IsElementaryDistinguishedSquare j g] (E : ModuleDerived X),
    (mayerVietorisRelativePushforwardTriangleFunctor f j g).obj E =
      mayerVietorisRelativePushforwardTriangle f j g E)

end AlgebraicGeometry.AlgebraicSpace.Modules
