/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.CountableGeneration
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory
open CategoryTheory.DerivedCategory CategoryTheory.ObjectProperty

universe u

/- Lemma 75.27.2: if `X` is a quasi-compact and quasi-separated algebraic space over a
scheme `S` whose structure sheaf has countable sections on every affine étale object, then
an object `K` of `D_QCoh(𝒪_X)` is a sequential homotopy colimit of perfect objects of
`D(𝒪_X)` if and only if every cohomology sheaf `Hⁱ(K)` has countable sections on affine
schemes étale over `X`. -/
@[stacks 0CRV] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.perfectHomotopyColimit_iff_countableAffineEtaleSections :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (hX : ∀ U : affineEtaleSite X, Countable (structureRing U.obj))
    (K : DerivedQCoh X),
    sequentialHomotopyColimits
      (fun E : ModuleDerived X ↦ ModuleDerived.IsPerfect E) K.obj ↔
      ∀ i : ℤ, ∀ U : affineEtaleSite X,
        Countable
          (sectionModule ((DerivedCategory.homologyFunctor (Modules X) i).obj K.obj) U.obj))
