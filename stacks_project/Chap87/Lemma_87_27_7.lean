module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.ClosedImmersion.Reduction
import StacksCheckRecall

/-!
# Closed immersions from monomorphisms through the reduction

A morphism of formal algebraic spaces that is representable by algebraic
spaces, a monomorphism, through which the reduction of the target factors,
and that is locally of finite type or has locally Noetherian target, is a
closed immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Lemma 87.27.7: A representable monomorphism containing the target reduction
is a closed immersion if it is locally of finite type or the target is locally
Noetherian. -/
@[stacks 0GHZ] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion.of_mono_of_reduction :
    ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
      [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
      (f : X ⟶ Y) [Mono f]
      (h_rep : AlgebraicSpace.representableByAlgebraicSpaces f)
      (R : ReductionData Y) (g : R.space.functorOfPoints ⟶ X)
      (h_factor : g ≫ f = R.ι)
      (h_lft_or_noetherian : LocallyOfFiniteType f ∨ IsLocallyNoetherian Y),
      ClosedImmersion f)
