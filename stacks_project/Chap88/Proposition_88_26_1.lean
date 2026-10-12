/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap88.«88_27_0_1_Completion»

/-!
# Rig glueing of morphisms

A morphism out of a locally Noetherian algebraic space is uniquely determined
by its restrictions to a complementary open and to the completion along the
closed subset, and every compatible pair of such restrictions glue when the
modification is proper and an isomorphism over that open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace completionAlong

/-- The fibre product of Hom-sets
`Mor_S(X', W) ×_{Mor_S(X'_/T, W)} Mor_S(X_/T, W)`, consisting of a morphism
`X' ⟶ W` and a morphism `X_/T ⟶ W` that agree on `X'_/T`. -/
structure GlueingHom {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X)
    (T : Closeds (Points X)) (W : AlgebraicSpace S) where
  /-- The morphism `X' ⟶ W`. -/
  hom : X' ⟶ W
  /-- The morphism `X_/T ⟶ W` of functors of points. -/
  completionHom : completionAlong X T ⟶ W.functorOfPoints
  /-- The two morphisms determine the same morphism `X'_/T ⟶ W`. -/
  compatible :
    map f T ≫ completionHom =
      ι X' (T.preimage (Points.continuous_map f)) ≫ hom

namespace GlueingHom

/-- The comparison map sending `w : X ⟶ W` to the compatible pair
`(f ≫ w, ι X T ≫ w)`. -/
def ofHom {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X)
    (T : Closeds (Points X)) (W : AlgebraicSpace S) (w : X ⟶ W) :
    GlueingHom f T W where
  hom := f ≫ w
  completionHom := ι X T ≫ w
  compatible := sorry

/-- Proposition 88.26.1: Let `S` be a scheme. Let `X` be a locally Noetherian
algebraic space over `S`. Let `T ⊂ Points X` be a closed subset with
complementary open subspace `U ⊂ X`. Let `f : X' ⟶ X` be a proper morphism of
algebraic spaces such that `f⁻¹U ⟶ U` is an isomorphism. For any algebraic
space `W` over `S`, the map
`Mor_S(X, W) ⟶ Mor_S(X', W) ×_{Mor_S(X'_/T, W)} Mor_S(X_/T, W)` is bijective.

Here `U` is `openComplementAlong X T`, `X_/T` is `completionAlong X T`,
`X'_/T` is `completionAlong X' (T.preimage (Points.continuous_map f))`, the
fibre product is `GlueingHom f T W`, and the comparison map is
`GlueingHom.ofHom f T W`. The isomorphism `f⁻¹U ⟶ U` is
`openInverseImageTo f (openComplementι X T)`. -/
@[stacks 0GI3]
theorem ofHom_bijective {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    [IsLocallyNoetherian X] (T : Closeds (Points X)) (f : X' ⟶ X)
    [Proper f] [IsIso (openInverseImageTo f (openComplementι X T))]
    (W : AlgebraicSpace S) :
    Function.Bijective (ofHom f T W) :=
  sorry

/-- The components of `ofHom f T W w` are precomposition with `f` and with
`ι X T`. -/
theorem ofHom_spec {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X)
    (T : Closeds (Points X)) {W : AlgebraicSpace S} (w : X ⟶ W) :
    (ofHom f T W w).hom = f ≫ w ∧
      (ofHom f T W w).completionHom = ι X T ≫ w :=
  sorry

/-- Every compatible pair in `GlueingHom f T W` arises from a unique morphism
`X ⟶ W`, when `X` is locally Noetherian, `f` is proper, and `f⁻¹U ⟶ U` is an
isomorphism. -/
theorem existsUnique {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    [IsLocallyNoetherian X] (T : Closeds (Points X)) (f : X' ⟶ X)
    [Proper f] [IsIso (openInverseImageTo f (openComplementι X T))]
    {W : AlgebraicSpace S} (p : GlueingHom f T W) :
    ∃! w : X ⟶ W, ofHom f T W w = p :=
  sorry

end GlueingHom

end completionAlong

end AlgebraicGeometry.AlgebraicSpace
