module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Injective
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Set

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Direct image along a proper morphism commutes with inverse image in a cartesian
square of schemes for every set-valued small étale sheaf. -/
@[stacks 0A3U]
theorem proper_baseChange_isIso {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) [IsProper f] :
    IsIso (BaseChange.setMap g f' g' f h_cart.flip F) := sorry

/-- The canonical comparison for a cartesian square with a proper direct-image
morphism is an isomorphism when the cartesian-square proof is supplied by `Fact`. -/
instance proper_baseChange_isIso_of_fact {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    [h_cart : Fact (IsPullback g' f' f g)]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) [IsProper f] :
    IsIso (BaseChange.setMap g f' g' f h_cart.out.flip F) :=
  proper_baseChange_isIso f g f' g' h_cart.out F

end AlgebraicGeometry.Scheme.Etale

namespace AlgebraicGeometry.Scheme.Hom

variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]

/-- For a proper morphism of schemes, the canonical étale base-change comparison
is an isomorphism in every cohomological degree for every cartesian square and
every locally torsion abelian étale sheaf. -/
@[stacks 095T]
theorem cohomologyCommutesWithBaseChange_of_isProper
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    CohomologyCommutesWithBaseChange f := sorry

end AlgebraicGeometry.Scheme.Hom
