module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism.Representable
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-! Lemma 67.53.1 -/
@[stacks 05Z4] #check (AlgebraicGeometry.AlgebraicSpace.universalHomeomorphism_presheaf_iff_universalHomeomorphism : ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S} {f : X ⟶ Y}, CategoryTheory.yoneda.relativelyRepresentable f → ((CategoryTheory.MorphismProperty.over (@AlgebraicGeometry.UniversalHomeomorphism : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})).presheaf f ↔ AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism f))

end AlgebraicGeometry.AlgebraicSpace
