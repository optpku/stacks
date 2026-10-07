module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import stacks_project.Chap69.Lemma_69_9_2_Injectives

/-!
# Vanishing of higher sections with support on an injective pushforward

For a closed immersion of algebraic spaces, the higher sheaves of sections with
support vanish on the direct image of an injective abelian sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `rightDerived`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 69.9.2: for a closed immersion `i : Z ⟶ X` of algebraic spaces over a scheme `S`
and an injective abelian sheaf `G` on the small étale site of `Z`, one has
`ℋ^p_Z((sheafPushforward i).obj G) = 0` for `p > 0`. -/
@[stacks 0A4N]
theorem closedImmersion_higherSectionsWithSupport_isZero
    {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    (sectionsWithSupport :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (adjunction : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupport)
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})]
    [sectionsWithSupport.Additive]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    (G : Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1}) [Injective G]
    (p : ℕ) (hp : 0 < p) :
    IsZero ((sectionsWithSupport.rightDerived p).obj
      ((sheafPushforward AddCommGrpCat.{u + 1} i).obj G)) := sorry

end AlgebraicGeometry.AlgebraicSpace
