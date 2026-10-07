module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_19_6_Stalk
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward

/-!
# Lemma 67.13.6

For a closed immersion of algebraic spaces, the small-étale stalk of a
pushed-forward sheaf of sets at the image geometric point is identified
with the stalk of the original sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.13.6: for a closed immersion `i : Z ⟶ X` of algebraic spaces over a
scheme `S`, a geometric point `zbar` of `Z`, and a sheaf `F` of sets on the
small étale site of `Z`, the stalk of `i_small,* F` at `zbar.map i` is
identified with the stalk of `F` at `zbar`. -/
@[stacks 0DK1]
theorem stalk_pushforward_closedImmersion
    {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf (smallEtaleTopology Z) (Type (u + 1))) (zbar : GeometricPoint Z) :
    Nonempty
      (GeometricPoint.stalk (zbar.map i) ((sheafPushforward (Type (u + 1)) i).obj F).1 ≃
        GeometricPoint.stalk zbar F.1) := sorry

end AlgebraicGeometry.AlgebraicSpace
