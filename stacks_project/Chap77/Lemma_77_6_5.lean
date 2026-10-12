/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap77.Lemma_77_3_2_Purity
public import stacks_project.Chap77.Theorem_77_4_7_FlatOver

/-!
# Lemma 77.6.5

A finite-type quasi-coherent module that is flat over `Y` is pure relative to
`Y` if and only if it is universally pure relative to `Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules
namespace IsPureOver

/-- Lemma 77.6.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a decent, finite type
morphism of algebraic spaces over `S`. Let `ℱ` be a finite type quasi-coherent
`𝒪_X`-module. Assume `ℱ` is flat over `Y`. In this case `ℱ` is pure relative to
`Y` if and only if `ℱ` is universally pure relative to `Y`.
Here `|X|` and `|Y|` are `Points X` and `Points Y`, flatness over `Y` is
`∀ x : Points X, flatOverAt ℱ f x`, purity relative to `Y` is `ℱ.IsPureOver f`,
and universal purity relative to `Y` is `ℱ.IsUniversallyPureOver f`. -/
@[stacks 0CW5]
theorem iff_universally_of_flatOver {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FiniteType f] [Decent f] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (h_flat : ∀ x : Points X, flatOverAt ℱ f x) :
    ℱ.IsPureOver f ↔ ℱ.IsUniversallyPureOver f :=
  sorry

end IsPureOver
end AlgebraicGeometry.AlgebraicSpace.Modules
