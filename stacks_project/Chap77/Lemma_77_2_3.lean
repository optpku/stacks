/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap68.Lemma_68_17_4_Relative
public import stacks_project.Chap77.Lemma_77_2_3_Impurity

/-!
# Descent of impurities along directed affine limits

An impurity of a finite-type quasi-coherent module over a directed inverse limit of
affine schemes over `Y` descends to an impurity at some finite stage.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules
namespace IsImpurity

/-- Lemma 77.2.3: in Situation 77.2.1, if `(g : T ⟶ Y, t' ⤳ t, ξ)` is an impurity of
`F` above `y` and `T` is a directed inverse limit of affine schemes over `Y`, then
for some `i` the image triple `(T_i ⟶ Y, t'_i ⤳ t_i, ξ_i)` is an impurity of `F`
above `y`. -/
@[stacks 0CV9]
theorem exists_stage {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FiniteType f] [Decent f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y)
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ SchemeOver Y)
    (hAff : ∀ i, IsAffine (D.obj i).left.left) (c : Cone D) (hc : IsLimit c)
    (t' t : c.pt.left.left) (ξ : Points (Limits.pullback f c.pt.hom))
    (h : IsImpurity f F y c.pt t' t ξ) :
    ∃ i, IsImpurity f F y (D.obj i) ((c.π.app i).left.left t')
      ((c.π.app i).left.left t) (Points.map (pullbackStageMap f c i) ξ) :=
  sorry

end IsImpurity
end AlgebraicGeometry.AlgebraicSpace.Modules
