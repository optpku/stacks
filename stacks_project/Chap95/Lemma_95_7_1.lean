module

public import stacks_project.Chap95.«95_7_0_1_Hom»
public import Mathlib.CategoryTheory.FiberedCategory.Cartesian

/-!
# Lemma 95.7.1

A morphism of Spaces is strongly cartesian if and only if the induced map
into the fibre product is an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces

/-- Lemma 95.7.1: a morphism `(f, g) = (φ.left, φ.right) : mk pX ⟶ mk pY` of Spaces
is strongly cartesian if and only if `f` induces an isomorphism
`toSigmaLeft pX pY φ : X ⟶ pullbackObj φ.right pY`, i.e. `X ⟶ U ×_{g, V} Y`. -/
@[stacks 04U9]
theorem isStronglyCartesian_iff {S : Scheme.{u}} {U V : Over S} {X Y : AlgebraicSpace S}
    (pX : X ⟶ ofOver U) (pY : Y ⟶ ofOver V) (φ : mk pX ⟶ mk pY) :
    p.IsStronglyCartesian φ.right φ ↔ IsIso (toSigmaLeft pX pY φ) := sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces
