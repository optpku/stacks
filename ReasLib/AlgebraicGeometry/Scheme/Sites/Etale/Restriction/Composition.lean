module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import Mathlib.CategoryTheory.Sites.Continuous

@[expose] public section

open CategoryTheory CategoryTheory.Functor

noncomputable section

universe u u₁ v₁

namespace AlgebraicGeometry.Scheme

/-- Restriction of sheaves along a composite of étale morphisms is canonically
isomorphic to successive restriction, for any coefficient category. -/
def etaleRestrictionSheafCompIso {U X V : Scheme.{u}}
    (j : U ⟶ X) (j' : V ⟶ U) [Etale j] [Etale j']
    (A : Type u₁) [Category.{v₁} A] :
    etaleRestrictionSheaf (j' ≫ j) A ≅
      etaleRestrictionSheaf j A ⋙ etaleRestrictionSheaf j' A :=
  (sheafPushforwardContinuousComp'
    (F := etaleRestriction j') (G := etaleRestriction j)
    (FG := etaleRestriction (j' ≫ j))
    ((MorphismProperty.Over.mapComp (⊤ : MorphismProperty Scheme)
      (inferInstance : Etale j') (inferInstance : Etale j) (j' ≫ j) rfl).symm :
      etaleRestriction j' ⋙ etaleRestriction j ≅ etaleRestriction (j' ≫ j))
    A V.smallEtaleTopology U.smallEtaleTopology X.smallEtaleTopology).symm

end AlgebraicGeometry.Scheme

end
