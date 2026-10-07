module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.ClosedSubscheme
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.52.7: a locally finite-type morphism to a locally Noetherian scheme
admits a closed subscheme through a fibre-closed point, quasi-finite there, while
retaining in a prescribed open a specializing point whose image leaves the fibre. -/
@[stacks 05GU] #check
  (AlgebraicGeometry.Scheme.Hom.exists_closedSubscheme_quasiFiniteAt_of_specializes :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      [IsLocallyNoetherian S] (x : X) (U : X.Opens),
      f.asFiber x ∈ closedPoints (f.fiber (f x)) →
      (∃ x' : X, x' ∈ U ∧ Specializes x' x ∧ f x' ≠ f x) →
      ∃ (Z : X.IdealSheafData) (hxZ : x ∈ Z.support),
        FiniteType.QuasiFiniteAt (Z.subschemeι ≫ f) ⟨x, hxZ⟩ ∧
          ∃ z : X, z ∈ Z.support ∧ z ∈ U ∧
            Specializes z x ∧ f z ≠ f x)

end AlgebraicGeometry.Scheme.Hom

end
