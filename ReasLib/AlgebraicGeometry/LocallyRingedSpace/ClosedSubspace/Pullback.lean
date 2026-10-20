module

public import Mathlib.CategoryTheory.Subobject.Limits
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.ClosedSubspace.Factorization
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.IdealSubobject.Pullback.LocalGeneration

/-!
# Pullbacks of associated closed subspaces

The inverse-image ideal is owned by `LocallyRingedSpace.IdealSubobject.pullback`.
This file records its universal closed-subspace property.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

section

variable {X Y Z Z' : LocallyRingedSpace.{u}}
variable {f : X ⟶ Y} {I : IdealSubobject Y} {i : Z ⟶ Y} {i' : Z' ⟶ X}

/-- The ideal of an inverse-image closed subspace is locally generated. -/
@[stacks 01HQ "pullback ideal local generation"]
theorem ClosedSubspace.IsAssociated.pullback_isLocallyGenerated
    (hi : ClosedSubspace.IsAssociated i I) (f : X ⟶ Y) :
    (I.pullback f).IsLocallyGeneratedBySections := sorry

/-- The composite from an inverse-image closed subspace to the original ambient space
annihilates the original defining ideal. -/
@[stacks 01HQ "pullback composite vanishing"]
theorem ClosedSubspace.IsAssociated.pullbackComposite_vanishing
    (hi : ClosedSubspace.IsAssociated i I)
    (hi' : ClosedSubspace.IsAssociated i' (I.pullback f)) :
    I.pullbackMap (i' ≫ f) = 0 := sorry

/-- Lemma 26.4.7 (2): the inverse-image closed subspace has a unique comparison morphism to the
original associated closed subspace. -/
@[stacks 01HQ "comparison morphism"]
theorem ClosedSubspace.IsAssociated.existsUnique_pullbackLift
    (hi : ClosedSubspace.IsAssociated i I)
    (hi' : ClosedSubspace.IsAssociated i' (I.pullback f)) :
    ∃! f' : Z' ⟶ Z, CommSq i' f' f i := sorry

/-- The inverse-image closed subspace admits a comparison morphism to the original one. -/
@[stacks 01HQ "existence of a pullback comparison"]
theorem ClosedSubspace.IsAssociated.exists_pullbackLift
    (hi : ClosedSubspace.IsAssociated i I)
    (hi' : ClosedSubspace.IsAssociated i' (I.pullback f)) :
    ∃ f' : Z' ⟶ Z, CommSq i' f' f i := sorry

/-- Comparison morphisms from an inverse-image closed subspace are unique. -/
@[stacks 01HQ "extensionality for pullback comparisons"]
theorem ClosedSubspace.IsAssociated.pullbackHom_ext
    (hi : ClosedSubspace.IsAssociated i I)
    {f₁ f₂ : Z' ⟶ Z}
    (h₁ : CommSq i' f₁ f i) (h₂ : CommSq i' f₂ f i) :
    f₁ = f₂ := sorry

/-- Lemma 26.4.7 (3): a comparison square with the inverse-image closed subspace is a pullback
square. -/
@[stacks 01HQ "pullback square"]
theorem ClosedSubspace.IsAssociated.isPullback_of_commSq
    (hi : ClosedSubspace.IsAssociated i I)
    (hi' : ClosedSubspace.IsAssociated i' (I.pullback f))
    (f' : Z' ⟶ Z) (hcomm : CommSq i' f' f i) :
    IsPullback i' f' f i := sorry

/-- The inverse-image closed subspace forms a pullback square with the original associated
closed subspace. -/
@[stacks 01HQ "existence of an associated pullback square"]
theorem ClosedSubspace.IsAssociated.exists_pullback
    (hi : ClosedSubspace.IsAssociated i I)
    (hi' : ClosedSubspace.IsAssociated i' (I.pullback f)) :
    ∃ f' : Z' ⟶ Z, IsPullback i' f' f i := sorry

end

end AlgebraicGeometry.LocallyRingedSpace
