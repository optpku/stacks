module

public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy.Orthogonal
public import ReasLib.CategoryTheory.ObjectProperty.Orthogonal.Retract

/-!
# K-Projective Differential Graded Modules

K-projectivity is intrinsically left orthogonality to acyclic objects in the DG homotopy
category.  This leaf exposes its module-level inverse image, its localization criterion, and its
closure properties.
-/

@[expose] public section

universe u v

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)

/-- A differential graded module is K-projective when its image in the homotopy category is left
orthogonal to every acyclic object. -/
@[stacks 09R0 "K-projective differential graded modules"]
def IsKProjective : ObjectProperty (DifferentialGradedModule.{u, v} A) :=
  (Homotopy.kProjective A).inverseImage (toK A)

/-- Module-level K-projectivity is the inverse image of intrinsic homotopy K-projectivity. -/
theorem isKProjective_iff (P : DifferentialGradedModule.{u, v} A) :
    IsKProjective A P ↔ Homotopy.kProjective A ((toK A).obj P) := sorry

/-- A DG-module is K-projective exactly when localization is bijective on every outgoing Hom
set from its homotopy object.  This is the module-level form of
`Homotopy.kProjective_iff_q_map_bijective`. -/
@[stacks 09R0]
theorem isKProjective_iff_q_map_bijective
    (P : DifferentialGradedModule.{u, v} A) :
    IsKProjective A P ↔
      ∀ M : DifferentialGradedModule.{u, v} A,
        Function.Bijective
          ((Derived.Q A).map :
            ((toK A).obj P ⟶ (toK A).obj M) →
              ((Derived.Q A).obj ((toK A).obj P) ⟶
                (Derived.Q A).obj ((toK A).obj M))) := sorry

namespace IsKProjective

/-- Module-level K-projectivity is stable under retracts of DG-modules. -/
instance isStableUnderRetracts :
    (IsKProjective A).IsStableUnderRetracts := sorry

end IsKProjective

namespace Homotopy

/-- Remark 22.36.1 (09R0): an intrinsic DG homotopy object is K-projective exactly when the
localization to the derived category is bijective on every outgoing Hom set. -/
@[stacks 09R0]
theorem kProjective_iff_q_map_bijective
    (P : K R (DifferentialGradedModule.{u, v} A)) :
    kProjective A P ↔
      ∀ M : K R (DifferentialGradedModule.{u, v} A),
        Function.Bijective
          ((Derived.Q A).map : (P ⟶ M) → ((Derived.Q A).obj P ⟶ (Derived.Q A).obj M)) := sorry

namespace KProjective

/-- The strictly full subcategory of K-projective objects in the intrinsic homotopy category. -/
@[stacks 09R0 "strictly full K-projective homotopy subcategory"]
abbrev subcategory := (kProjective A).FullSubcategory

/-- K-projective DG homotopy objects form a triangulated object property. -/
instance isTriangulated : (kProjective A).IsTriangulated := sorry

/-- K-projectivity is stable under retracts in the DG homotopy category. -/
instance isStableUnderRetracts : (kProjective A).IsStableUnderRetracts := sorry

end KProjective

#synth (kProjective A).IsClosedUnderIsomorphisms
#synth (kProjective A).IsTriangulated
#synth (kProjective A).IsStableUnderRetracts

end Homotopy

#synth (IsKProjective A).IsStableUnderRetracts
#synth (IsKProjective A).IsClosedUnderIsomorphisms

end DifferentialGradedModule
