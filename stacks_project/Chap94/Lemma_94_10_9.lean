module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property
import StacksCheckRecall

/-!
# Monotonicity of having a morphism property

If `P ≤ P'` as properties of morphisms of algebraic spaces in the sense of
Definition 94.10.1, then a 1-morphism representable by algebraic spaces that
has `P` also has `P'`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/- Lemma 94.10.9: let `S` be a scheme in `Sch_fppf`. Let `X` and `Y` be
categories fibred in groupoids over `(Sch/S)_fppf`. Let `f : X ⟶ Y` be a
1-morphism representable by algebraic spaces. Let `P` and `P'` be properties
of morphisms of algebraic spaces as in Definition 94.10.1, so each is stable
under base change and fppf local on the target. If `P ≤ P'`, then `has P f`
implies `has P' f`. -/
@[stacks 045F]
#check (AlgebraicGeometry.Groupoids.Hom.has.of_le :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {P P' : MorphismProperty (AlgebraicSpace S)}
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    [P'.IsStableUnderBaseChange]
    [P'.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f)
    (h : P ≤ P') (hfP : has P f), has P' f)

end AlgebraicGeometry.Groupoids.Hom
