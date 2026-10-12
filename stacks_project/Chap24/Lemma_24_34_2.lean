/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.QuasiIso
public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.Closure
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Equivalence
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped DifferentialGradedCategory DifferentialGradedModule

noncomputable section

universe u v

namespace CochainDGAlgebra.Hom.Derived

section

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, v} R}
variable (f : A ⟶ B) (hf : CochainDGAlgebra.quasiIso f)
variable {P : ObjectProperty (DifferentialGradedModule.Derived.Category A)}
variable {Q : ObjectProperty (DifferentialGradedModule.Derived.Category B)}
variable [Q.IsClosedUnderIsomorphisms]
variable (hQC : Q.inverseImage (equivalence f hf).functor = P)

/- Lemma 24.34.2 (tag 0GZF), reusable algebraic core: the canonical derived equivalence
restricts to the two full subcategories once quasi-coherence is identified under extension.
The source specialization still needs sheaf-DGA extension and that property equality. -/
@[stacks 0GZF "restricted DGA derived equivalence; sheaf-QC comparison pending"]
#check
  (ObjectProperty.FullSubcategory.restrict.isEquivalence_of_inverseImage_eq
      (equivalence f hf).functor hQC :
    (ObjectProperty.FullSubcategory.restrict (equivalence f hf).functor
      (le_of_eq hQC.symm)).IsEquivalence)

/- The ambient equivalence has derived extension of scalars as its forward functor. -/
#check (equivalence_functor f hf : (equivalence f hf).functor = extension f)

end

end CochainDGAlgebra.Hom.Derived
