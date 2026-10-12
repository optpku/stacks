/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap77.Lemma_77_3_2_Purity
public import stacks_project.Chap77.Theorem_77_4_7_FlatOver

/-!
# Lemma 77.6.4

A finite-type quasi-coherent module that is flat at every point of the fibre
over `y` and pure above `y` is universally pure above `y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules
namespace IsPureAlong

/-- Lemma 77.6.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Let `ℱ` be a quasi-coherent `𝒪_X`-module. Let `y ∈ |Y|`. Assume
`f` is decent and of finite type, `ℱ` is of finite type, `ℱ` is flat over `Y` at
all points lying over `y`, and `ℱ` is pure above `y`. Then `ℱ` is universally
pure above `y`.
Here `|Y|` is `Points Y`, the points of `|X|` lying over `y` are
`Points.map f ⁻¹' {y}`, flatness at a point is `flatOverAt ℱ f`, pure above `y`
is `ℱ.IsPureAlong f y`, and universally pure above `y` is
`ℱ.IsUniversallyPureAlong f y`. -/
@[stacks 0CW4]
theorem universally_of_flatOverAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FiniteType f] [Decent f] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (y : Points Y)
    (h_flat : ∀ x ∈ Points.map f ⁻¹' {y}, flatOverAt ℱ f x)
    (h_pure : ℱ.IsPureAlong f y) :
    ℱ.IsUniversallyPureAlong f y :=
  sorry

end IsPureAlong
end AlgebraicGeometry.AlgebraicSpace.Modules
