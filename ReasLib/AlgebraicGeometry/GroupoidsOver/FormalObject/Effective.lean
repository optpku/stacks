module

public import Mathlib.CategoryTheory.EssentialImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Approximation

/-!
# Effective formal objects

A formal object of a category fibred in groupoids over `(Sch/S)_fppf` is
effective when it lies in the essential image of the approximation functor
from complete local objects.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.FormalObject

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}

/-- A formal object is effective if it lies in the essential image of the
approximation functor from objects over complete local finite-type-residue
spectra. -/
class IsEffective (ξ : FormalObject X) : Prop where
  /-- The formal object is isomorphic to the approximation of some complete
  local object. -/
  mem_essImage : (GroupoidsOver.approximation X).essImage ξ

/-- The approximation of an object over a complete local spectrum is effective. -/
instance instIsEffective_obj (x : CompleteLocalObject X) :
    IsEffective ((GroupoidsOver.approximation X).obj x) where
  mem_essImage := Functor.obj_mem_essImage (GroupoidsOver.approximation X) x

/-- Effectiveness is membership in the essential image of approximation. -/
theorem isEffective_iff {ξ : FormalObject X} :
    IsEffective ξ ↔ (GroupoidsOver.approximation X).essImage ξ :=
  sorry

/-- A formal object is effective if and only if it is isomorphic to the
approximation of some complete local object. -/
theorem isEffective_iff_exists {ξ : FormalObject X} :
    IsEffective ξ ↔
      ∃ x : CompleteLocalObject X,
        Nonempty ((GroupoidsOver.approximation X).obj x ≅ ξ) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.FormalObject
