module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/-!
# Definition 29.38.1

The reusable relative-very-ampleness owner is maintained in
`ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery`.
-/

/- Definition 29.38.1: an invertible module is relatively very ample exactly when it is the
pullback of the tautological module along an immersion into a projective bundle over the base. -/
@[stacks 01VM] #check
  (AlgebraicGeometry.RelativelyVeryAmple.iff :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S} {L : X.Modules},
      AlgebraicGeometry.RelativelyVeryAmple f L ↔
        AlgebraicGeometry.Scheme.Modules.Invertible L ∧
          ∃ (P : AlgebraicGeometry.Scheme.{u}) (π : P ⟶ S) (ℰ : S.Modules),
            ℰ.IsQuasicoherent ∧
              ∃ (hπ : AlgebraicGeometry.Scheme.ProjectiveBundle.Representation π ℰ)
                (i : X ⟶ P),
                AlgebraicGeometry.IsImmersion i ∧
                  i ≫ π = f ∧
                    Nonempty
                      (L ≅
                        (AlgebraicGeometry.Scheme.Modules.pullback i).obj
                          (AlgebraicGeometry.Scheme.ProjectiveBundle.tautologicalSheaf π hπ)))
