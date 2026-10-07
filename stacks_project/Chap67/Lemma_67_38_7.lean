module

public import stacks_project.Chap67.Definition_67_27_1_QuasiFinite
public import stacks_project.Chap67.Lemma_67_27_6_LocallyQuasiFinite
public import stacks_project.Chap67.Lemma_67_38_5_Unramified

/-!
# Unramified morphisms of algebraic spaces are locally quasi-finite
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace UnramifiedAt

/-- Lemma 67.38.7 (1): If `f` is unramified at `x` then `f` is quasi-finite at
`x`. -/
@[stacks 05W0]
theorem quasiFiniteAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {x : Points X} (h : UnramifiedAt f x) : FiniteType.QuasiFiniteAt f x :=
  sorry

end UnramifiedAt

/-- Lemma 67.38.7 (2): An unramified morphism of algebraic spaces is locally
quasi-finite. -/
@[stacks 05W0]
instance locallyQuasiFinite_of_unramified {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Unramified f] :
    LocallyQuasiFinite f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
