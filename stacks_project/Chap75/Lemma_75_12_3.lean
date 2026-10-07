module

public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import stacks_project.Chap67.Lemma_67_11_2_Pushforward
public import stacks_project.Chap67.Lemma_67_30_5_Flat

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

/-- Lemma 75.12.3. Let `S` be a scheme. Let `f : X ⟶ Y` be a flat, quasi-compact,
and quasi-separated morphism of algebraic spaces over `S`. If `J` is an injective
object of `QCoh X`, then `f_* J` is an injective object of `QCoh Y`. -/
@[stacks 09TK]
theorem pushforward.injective_obj
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [Flat f]
    (J : QCoh X) (hJ : Injective J) :
    Injective ((pushforward f).obj J) :=
  sorry

/-- Quasi-coherent pushforward along a flat qcqs morphism of algebraic spaces
preserves injective objects. -/
instance pushforward.preservesInjectiveObjects
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [Flat f] :
    (pushforward f).PreservesInjectiveObjects :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.QCoh
