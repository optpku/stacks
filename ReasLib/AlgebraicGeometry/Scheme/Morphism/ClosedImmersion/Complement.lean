module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Complements of closed immersions

This file defines the open subscheme complementary to the image of a closed immersion.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The open complement of the image of a closed immersion of schemes. -/
def closedImmersionComplement {S Z : Scheme.{u}} (i : Z ⟶ S) [IsClosedImmersion i] : S.Opens :=
  ⟨(Set.range ⇑(CategoryTheory.ConcreteCategory.hom i.base))ᶜ,
    (isOpen_compl_iff).2 (IsClosedImmersion.isClosedEmbedding i).isClosed_range⟩

/-- A scheme morphism is an isomorphism over the open complement of a closed immersion
if its base change to that open subscheme is an isomorphism. -/
def IsIsoOverComplement {X' X Z : Scheme.{u}} (f : X' ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] : Prop :=
  IsIso (Limits.pullback.snd f (closedImmersionComplement i).ι)

/-- Being an isomorphism over the complement is equivalent to invertibility of the
base-changed projection to the complementary open subscheme. -/
theorem isIsoOverComplement_iff {X' X Z : Scheme.{u}} (f : X' ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] :
    IsIsoOverComplement f i ↔
      IsIso (Limits.pullback.snd f (closedImmersionComplement i).ι) := Iff.rfl

end AlgebraicGeometry
