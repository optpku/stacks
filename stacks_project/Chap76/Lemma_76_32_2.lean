/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Specialization.Dimension
public import stacks_project.Chap68.Definition_68_25_4_UniversallyCatenary
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap76.Lemma_76_32_2_DimensionFunction

/-!
# Dimension functions along locally finite-type morphisms of algebraic spaces

A dimension function on a decent locally Noetherian universally catenary
algebraic space induces a dimension function on a decent algebraic space
locally of finite type over it.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- Lemma 76.32.2: Let `S` be a scheme. Let `B` be a decent locally Noetherian
universally catenary algebraic space over `S`, and let `δ : Points B → ℤ` be a
dimension function. If `X` is a decent algebraic space over `B` whose structure
morphism `f : X ⟶ B` is locally of finite type, then
`(relativeDimensionFunction f) δ`, given by
`x ↦ δ (Points.map f x) + (residueFieldTrdegAt f x : ℤ)`, is a dimension
function on `Points X`. -/
@[stacks 0EDN]
instance instIsDimensionFunction_relativeDimensionFunction {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] (f : X ⟶ B) [IsDecent X]
    [LocallyOfFiniteType f] (δ : Points B → ℤ) [IsDimensionFunction δ] :
    IsDimensionFunction ((relativeDimensionFunction f) δ) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
