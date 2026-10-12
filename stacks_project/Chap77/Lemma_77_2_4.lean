/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap68.Lemma_68_17_4_Relative
public import stacks_project.Chap77.Definition_77_2_2_Impurity

/-!
# Flat ascent of impurities

A morphism of pointed algebraic spaces that is flat at the selected point lifts
an impurity of a finite-type quasi-coherent module to an impurity of the
pullback, étale over the original base-change scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules
namespace Impurity

/-- Lemma 77.2.4: in Situation 77.2.1, a morphism of pointed algebraic spaces
`(Y1, y1) ⟶ (Y, y)` that is flat at `y1` lifts an impurity of `F` above `y` to
an impurity of the pullback of `F` to `X1 = Y1 ×_Y X` above `y1`, with the new
base scheme `T1` étale over `Y1 ×_Y T`. -/
@[stacks 0CVA]
theorem exists_of_flatAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y)
    {Y1 : AlgebraicSpace S} (φ : Y1 ⟶ Y) {y1 : Points Y1}
    (h_map : Points.map φ y1 = y) (h_flat : FlatAt φ y1)
    (I : Impurity F f y) :
    ∃ (I1 : Impurity ((Modules.pullback (Limits.pullback.fst f φ)).obj F)
        (Limits.pullback.snd f φ) y1)
      (π : ofOver I1.T ⟶ Limits.pullback φ I.g),
      AlgebraicSpace.Etale π ∧ I1.g = π ≫ Limits.pullback.fst φ I.g :=
  sorry

end Impurity
end AlgebraicGeometry.AlgebraicSpace.Modules
