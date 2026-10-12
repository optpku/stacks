/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.CountableGeneration
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty

universe u v

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)
variable (hA : A.HasCountableCohomology)
variable (X : DifferentialGradedModule.Derived.Category.{u, v} A)

/- Lemma 22.38.3 (0CRM): for a DGA with countable cohomology, a derived module has
countable cohomology in every degree exactly when it is a sequential homotopy colimit of
compact objects. -/
@[stacks 0CRM] #check
  (DifferentialGradedModule.Derived.sequentialHomotopyColimits_iff_countableHomology
      A hA X :
    sequentialHomotopyColimits (IsCompactObject : ObjectProperty
      (DifferentialGradedModule.Derived.Category.{u, v} A)) X ↔
      DifferentialGradedModule.Derived.countableHomology A X)

/- The DGA-specific theorem is obtained from the reusable compact weak-generator criterion by
using the regular derived module and identifying its shifted represented Hom types with
cohomology. -/
#check @CategoryTheory.IsCompactObject.sequentialHomotopyColimits_iff_countableShiftedHom
#check @DifferentialGradedModule.Derived.countableShiftedHomFrom_regularObject_iff
