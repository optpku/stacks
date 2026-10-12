/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_26_6_Pullback

/-!
# Derived pullback of quasi-coherent complexes on algebraic spaces

`Lf^*` along a morphism of algebraic spaces preserves `D_QCoh`, so an object of
`D_QCoh(𝒪_X)` has a named lift `pullbackObj` in `D_QCoh(𝒪_Y)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Derived pullback along a morphism of algebraic spaces preserves quasi-coherent
cohomology. -/
theorem pullbackObj_mem {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X)
    (E : DerivedQCoh X) :
    derivedQuasiCoherentModuleProperty Y ((ModuleDerived.pullback f).obj E.obj) :=
  sorry

/-- The object `L f^* E` of `D_QCoh(𝒪_Y)` obtained from `E` in `D_QCoh(𝒪_X)`. -/
noncomputable def pullbackObj {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X)
    (E : DerivedQCoh X) : DerivedQCoh Y where
  obj := (ModuleDerived.pullback f).obj E.obj
  property := pullbackObj_mem f E

/-- The underlying derived module of `pullbackObj` is ordinary derived pullback. -/
theorem pullbackObj_obj {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X)
    (E : DerivedQCoh X) :
    (pullbackObj f E).obj = (ModuleDerived.pullback f).obj E.obj :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
