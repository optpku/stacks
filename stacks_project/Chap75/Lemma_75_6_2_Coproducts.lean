module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import stacks_project.Chap75.Lemma_75_6_1_Pushforward
public import stacks_project.Chap75.Lemma_75_5_3_Coproducts

/-!
# Coproducts and derived pushforward of algebraic spaces

Restricted derived pushforward along a quasi-compact, quasi-separated morphism of
algebraic spaces preserves coproducts of complexes with quasi-coherent cohomology.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforward

/-- Derived pushforward along a quasi-compact and quasi-separated morphism of algebraic
spaces preserves coproducts indexed by types in the ambient universe. -/
instance preservesCoproducts {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (pushforward f) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforward
