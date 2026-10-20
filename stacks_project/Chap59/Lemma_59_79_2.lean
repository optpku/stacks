module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Acyclicity
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/- Lemma 59.79.2: for a closed immersion `i : Z ⟶ X` and an injective abelian sheaf `G` on
`Z.smallEtaleTopology`, the positive right-derived functors of the sheaf of sections with support
in `Z` vanish on the direct image `i_* G`. -/
@[stacks 09XR] #check
  (AlgebraicGeometry.Scheme.Etale.sectionsWithSupport_rightDerived_isZero_of_injective :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [Abelian (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
    [(Scheme.Etale.sectionsWithSupport i).Additive]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) [Injective G]
    (p : ℕ) (hp : 0 < p),
    IsZero (((Scheme.Etale.sectionsWithSupport i).rightDerived p).obj
      ((Scheme.etaleAbelianPushforward i).obj G)))
