/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Retraction
import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Differentials.Composition
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Sections
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Differentials

/-!
# Splittings of conormal sequences

Retractions of an immersion over a base split its canonical conormal-differentials complex.
The same condition on target-open neighborhoods gives a local splitting, and a section makes
the canonical conormal map an isomorphism.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.Conormal.Differentials

variable {Z X S : Scheme.{u}}

/-- The canonical conormal-differentials complex of an immersion is split on target-open
neighborhoods of the images of all source points. -/
def IsLocallySplit (i : Z ⟶ X) [IsImmersion i] (f : X ⟶ S) : Prop :=
  ∀ z : Z, ∃ U : X.Opens, i.base z ∈ U ∧
    Nonempty ((complex (i ∣_ U) (U.ι ≫ f)).Splitting)

/-- Local splitting of the canonical conormal-differentials complex is equivalent to the
existence of a splitting on a target-open neighborhood of every source point. -/
theorem isLocallySplit_iff (i : Z ⟶ X) [IsImmersion i] (f : X ⟶ S) :
    IsLocallySplit i f ↔
      ∀ z : Z, ∃ U : X.Opens, i.base z ∈ U ∧
        Nonempty ((complex (i ∣_ U) (U.ι ≫ f)).Splitting) :=
  Iff.rfl

/-- A retraction of an immersion over a base splits its canonical
conormal-differentials complex. -/
theorem complex_splitting_of_hasRetraction
    (i : Z ⟶ X) [IsImmersion i] (f : X ⟶ S)
    (h : HasRetractionOver i f) :
    Nonempty ((complex i f).Splitting) := sorry

/-- Target-locally defined retractions of an immersion over a base yield target-local
splittings of its canonical conormal-differentials complex. -/
theorem locallySplit_of_locallyHasRetraction
    (i : Z ⟶ X) [IsImmersion i] (f : X ⟶ S)
    (h : LocallyHasRetractionOver i f) :
    IsLocallySplit i f := sorry

/-- For a section of a scheme morphism, the canonical conormal map to the pullback of relative
differentials is an isomorphism. -/
theorem map_isIso_of_section
    (f : X ⟶ S) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) :
    IsIso (map s f) := sorry

end AlgebraicGeometry.Scheme.Hom.Conormal.Differentials
