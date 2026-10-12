/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyI.Embedding
public import ReasLib.Algebra.Homology.DifferentialGradedModule.QuasiIso

/-!
# Property I resolutions
-/

@[expose] public section

universe u v

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedModule.PropertyI

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)

/-- A property I resolution of `M` is a specified quasi-isomorphism to a specified right DG
module equipped with a concrete property I filtration. -/
@[stacks 09KU "property-I resolutions"]
structure Resolution (M : DifferentialGradedModule.{u, v} A) where
  /-- The resolving right DG module. -/
  obj : DifferentialGradedModule.{u, v} A
  /-- The comparison map from the original module to the resolving module. -/
  ι : M ⟶ obj
  /-- A chosen property I filtration of the resolving module. -/
  filtration : Filtration A obj
  /-- The comparison map is a quasi-isomorphism. -/
  quasiIso_ι : quasiIso A ((toK A).map ι)

namespace Resolution

/-- The resolving object of a property I resolution has property I. -/
@[stacks 09KU "property I of a resolution object"]
theorem propertyI_obj {M : DifferentialGradedModule.{u, v} A} (I : Resolution A M) :
    HasPropertyI A I.obj := sorry

/-- Lemma 22.21.4 (09KU): every right DG `A`-module admits a property I resolution. -/
@[stacks 09KU]
theorem nonempty (M : DifferentialGradedModule.{u, v} A) :
    Nonempty (Resolution A M) := sorry

end Resolution

end DifferentialGradedModule.PropertyI
