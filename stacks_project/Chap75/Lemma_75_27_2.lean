/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.CompactObject.CountableGeneration
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Lemma_66_18_6_Site
public import stacks_project.Chap66.Lemma_66_31_3_LocallyProjective
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory
open CategoryTheory.DerivedCategory CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Lemma 75.27.2: if `X` is a quasi-compact and quasi-separated algebraic space over a
scheme `S` whose structure sheaf has countable sections on every affine étale object, then
an object `K` of `D_QCoh(𝒪_X)` is a sequential homotopy colimit of perfect objects of
`D(𝒪_X)` if and only if every cohomology sheaf `Hⁱ(K)` has countable sections on affine
schemes étale over `X`. -/
@[stacks 0CRV]
theorem perfectHomotopyColimit_iff_countableAffineEtaleSections
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (hX : ∀ U : affineEtaleSite X, Countable (structureRing U.obj))
    (K : DerivedQCoh X) :
    sequentialHomotopyColimits
      (fun E : ModuleDerived X ↦ ModuleDerived.IsPerfect E) K.obj ↔
      ∀ i : ℤ, ∀ U : affineEtaleSite X,
        Countable
          (sectionModule ((DerivedCategory.homologyFunctor (Modules X) i).obj K.obj) U.obj) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
