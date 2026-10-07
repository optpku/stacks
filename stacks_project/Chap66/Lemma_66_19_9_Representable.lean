module

public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Pullback
public import stacks_project.Chap66.Lemma_66_18_8_Pullback
public import stacks_project.Chap66.Lemma_66_18_8_Topos

/-!
# Inverse image of sheafified representables on étale sites of algebraic spaces

For an étale morphism `V → Y` of algebraic spaces, inverse image along `f_spaces,étale`
identifies `h_V` with `h_{X ×_Y V}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Functor.SheafifiedRepresentable

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Inverse image of a sheafified representable `h_V` along `f_spaces,étale` is
`h_{X ×_Y V}`. Under the identification of Lemma 66.18.3 this is `f_small⁻¹ h_V`. -/
noncomputable def smallEtaleInverseImage_representableIso (V : spacesEtaleSite Y) :
    ((spacesEtalePullback f).sheafPullback (Type (u + 1))
        (spacesEtaleTopology Y) (spacesEtaleTopology X)).obj
      ((spacesEtaleTopology Y).uliftSheafifiedRepresentable.{u + 1, u + 1, u + 1} V) ≅
      (spacesEtaleTopology X).uliftSheafifiedRepresentable.{u + 1, u + 1, u + 1}
        ((spacesEtalePullback f).obj V) :=
  (pullbackIso.{u + 1, u + 1, u + 1, u + 1, u + 1} (spacesEtalePullback f)
      (spacesEtaleTopology Y) (spacesEtaleTopology X) V).symm

/-- The representable identification is the inverse of the generic sheafified-representable
pullback isomorphism. -/
theorem smallEtaleInverseImage_representableIso_eq_pullbackIso (V : spacesEtaleSite Y) :
    smallEtaleInverseImage_representableIso f V =
      (pullbackIso.{u + 1, u + 1, u + 1, u + 1, u + 1} (spacesEtalePullback f)
          (spacesEtaleTopology Y) (spacesEtaleTopology X) V).symm :=
  sorry

/-- The forward map of the representable identification. -/
theorem smallEtaleInverseImage_representableIso_hom (V : spacesEtaleSite Y) :
    (smallEtaleInverseImage_representableIso f V).hom =
      (pullbackIso.{u + 1, u + 1, u + 1, u + 1, u + 1} (spacesEtalePullback f)
          (spacesEtaleTopology Y) (spacesEtaleTopology X) V).inv :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
