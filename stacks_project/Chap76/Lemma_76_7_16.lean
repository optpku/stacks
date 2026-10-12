/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap76.Definition_76_7_2_Differentials

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Lemma 76.7.16: let `S` be a scheme. Let `f : X ⟶ Y` be a smooth morphism of algebraic
spaces over `S`. Then `Ω[f]` is a finite locally free `𝒪_X`-module. -/
@[stacks 0CK5]
instance isFiniteLocallyFree_relativeDifferentials_of_smooth
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicSpace.Smooth f] :
    (relativeDifferentials f).IsFiniteLocallyFree :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
