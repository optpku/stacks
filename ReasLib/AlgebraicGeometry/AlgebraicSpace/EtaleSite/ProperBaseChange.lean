module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.BaseChangeComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper

/-! Proper base change for sheaves on the small étale site of an algebraic
space. -/
@[expose] public section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped MorphismOfTopoiIn
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace
variable {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))

/-- For a proper morphism, the canonical small étale base-change comparison is
an isomorphism in every cartesian square. -/
@[stacks 0DG0]
theorem proper_baseChange_isIso [Proper f] :
    IsIso (smallEtaleBaseChangeHom f g f' g' h_cart F) := sorry

/-- The proper base-change comparison is an isomorphism when its cartesian
square is supplied through a canonical `Fact` instance. -/
instance proper_baseChange_isIso_of_fact [h_cart : Fact (IsPullback g' f' f g)]
    [Proper f] :
    IsIso (smallEtaleBaseChangeHom f g f' g' h_cart.out F) :=
  proper_baseChange_isIso f g f' g' h_cart.out F
end AlgebraicGeometry.AlgebraicSpace
