module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery.PointSeparation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.22.2: over an infinite field, a relatively very ample module on a finite-type scheme
has a global section vanishing at a rational point and nonvanishing at every member of a finite
family of other points. -/
@[stacks 0B58]
#check (AlgebraicGeometry.RelativelyVeryAmple.exists_section_vanishingAt_nonvanishingAt :
  ∀ {k : Type u} [Field k] [Infinite k]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)} [Scheme.Hom.FiniteType f]
    {L : X.Modules} (hL : RelativelyVeryAmple f L)
    (x : X) [IsIso (f.residueFieldMap x)]
    {n : ℕ} (xs : Fin n → X) (hxs : ∀ i : Fin n, x ≠ xs i),
    ∃ s : L.sections,
      x ∉ RingedSpace.sectionNonvanishingLocus X.toRingedSpace L s ∧
        ∀ i : Fin n, xs i ∈ RingedSpace.sectionNonvanishingLocus X.toRingedSpace L s)
