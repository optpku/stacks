/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_26_6_Pullback
public import stacks_project.Chap75.Lemma_75_26_4_VectorBundle
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Homology

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules
open DerivedCategory.TStructure ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {Y X : AlgebraicSpace S}

def tryInv (g : Y ⟶ X) (M : X.Modules) (i : ℤ) :
    (DerivedCategory.singleFunctor (Modules Y) i).obj ((Modules.pullback g).obj M) ⟶
      DerivedCategory.Q.obj
        (((Modules.pullback g).mapHomologicalComplex (up ℤ)).obj
          ((CochainComplex.singleFunctor (Modules X) i).obj M)) :=
  (Functor.Homotopy.singleIso (Modules.pullback g) i).inv.app M ≫
    (Functor.Homotopy.cochainIso (Modules.pullback g)).hom.app
      ((CochainComplex.singleFunctor (Modules X) i).obj M)

def tryInv2 (g : Y ⟶ X) (M : X.Modules) (i : ℤ) :
    (DerivedCategory.singleFunctor (Modules Y) i).obj ((Modules.pullback g).obj M) ⟶
      (DerivedCategory.singleFunctor (Modules Y) i).obj ((Modules.pullback g).obj M) :=
  tryInv g M i ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
          (Modules.pullback g) (up ℤ) i).hom.app M)

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
