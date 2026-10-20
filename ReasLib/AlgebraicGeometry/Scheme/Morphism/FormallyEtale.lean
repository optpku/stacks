module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.RingTheory.Etale.Basic

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A morphism of schemes is formally étale when its maps on affine coordinate rings are
formally étale. -/
class FormallyEtale (f : X ⟶ S) : Prop where
  /-- The induced ring map on compatible affine opens is formally étale. -/
  formallyEtale_appLE (f) :
    ∀ {U : S.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V)
      (e : V ≤ f ⁻¹ᵁ U), (f.appLE U V e).hom.FormallyEtale

namespace Scheme.Hom

/-- Formal étaleness supplies formal étaleness of the induced map on affine coordinate
rings. -/
alias formallyEtale_appLE := FormallyEtale.formallyEtale_appLE

end Scheme.Hom

namespace FormallyEtale

/-- Scheme-level formal étaleness is associated with ring-level formal étaleness. -/
instance instHasRingHomProperty :
    HasRingHomProperty (@FormallyEtale.{u}) RingHom.FormallyEtale := sorry

/-- A morphism between affine schemes is formally étale if and only if its induced map on
global sections is formally étale. -/
theorem iff_of_isAffine [IsAffine X] [IsAffine S] :
    FormallyEtale f ↔ f.appTop.hom.FormallyEtale := sorry

/-- Formally étale scheme morphisms are stable under composition. -/
instance instIsStableUnderComposition :
    MorphismProperty.IsStableUnderComposition (@FormallyEtale.{u}) := sorry

/-- Formal étaleness contains identities and is stable under composition. -/
instance instIsMultiplicative :
    MorphismProperty.IsMultiplicative (@FormallyEtale.{u}) := sorry

/-- Formally étale scheme morphisms are stable under base change. -/
instance instIsStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange (@FormallyEtale.{u}) := sorry

/-- Every formally étale scheme morphism is formally unramified. -/
instance toFormallyUnramified [FormallyEtale f] : FormallyUnramified f := sorry

/-- Formal étaleness is equivalent to unique lifting from affine first-order thickenings. -/
theorem iff_existsUnique_lift :
    FormallyEtale f ↔
      ∀ {T T' : Scheme.{u}} [IsAffine T] [IsAffine T'] (i : T ⟶ T')
        [IsClosedImmersion i] (hi : i.ker ^ 2 = ⊥) (g : T ⟶ X) (h : T' ⟶ S)
        (sq : CommSq g i f h), Nonempty (Unique sq.LiftStruct) := sorry

/-- A formally étale scheme morphism has a unique lift from every affine first-order
thickening. -/
theorem existsUnique_lift [FormallyEtale f] {T T' : Scheme.{u}} [IsAffine T] [IsAffine T']
    (i : T ⟶ T') [IsClosedImmersion i] (hi : i.ker ^ 2 = ⊥) (g : T ⟶ X)
    (h : T' ⟶ S) (sq : CommSq g i f h) : Nonempty (Unique sq.LiftStruct) := sorry

/-- The unique lifting property for affine first-order thickenings implies formal étaleness. -/
theorem of_existsUnique_lift
    (h_lift : ∀ {T T' : Scheme.{u}} [IsAffine T] [IsAffine T'] (i : T ⟶ T')
      [IsClosedImmersion i] (hi : i.ker ^ 2 = ⊥) (g : T ⟶ X) (h : T' ⟶ S)
      (sq : CommSq g i f h), Nonempty (Unique sq.LiftStruct)) : FormallyEtale f := sorry

end FormallyEtale

end AlgebraicGeometry
