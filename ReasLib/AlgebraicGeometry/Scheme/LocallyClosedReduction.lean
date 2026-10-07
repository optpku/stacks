module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced
public import ReasLib.Topology.LocallyClosed.Subsets

/-!
# Reduced induced schemes on locally closed subsets

The open ambient subscheme, closed subset, vanishing ideal, resulting scheme,
and immersion are all explicit reusable data.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.LocallyClosedReduction

variable {X : Scheme.{u}}

/-- The open complement of the boundary of a bundled locally closed subset. -/
@[stacks 0F2L "ambient open of a locally closed reduction"]
def ambientOpen (T : LocallyCloseds X) : X.Opens :=
  ⟨coborder T, T.property.isOpen_coborder⟩

/-- The underlying set of the ambient open is the coborder of `T`. -/
@[simp, stacks 0F2L "ambient open underlying set"]
theorem coe_ambientOpen (T : LocallyCloseds X) :
    (ambientOpen T : Set X) = coborder T := sorry

/-- The locally closed subset, viewed as a closed subset of its ambient open subscheme. -/
@[stacks 0F2L "closed subset in the ambient open"]
def closedSubset (T : LocallyCloseds X) :
    Closeds (ambientOpen T).toScheme :=
  ⟨(ambientOpen T).ι ⁻¹' T, isClosed_preimage_val_coborder⟩

/-- The closed subset is the inverse image of `T` under the open-subscheme inclusion. -/
@[stacks 0F2L "locally closed subset in the ambient open"]
theorem coe_closedSubset (T : LocallyCloseds X) :
    (closedSubset T : Set (ambientOpen T).toScheme) =
      (ambientOpen T).ι ⁻¹' T := sorry

/-- The reduced closed-subscheme structure on the locally closed subset inside its ambient
open. -/
@[stacks 0F2L "closed stage of a locally closed reduction"]
noncomputable abbrev closedStructure (T : LocallyCloseds X) :
    ClosedSubschemeStructure (closedSubset T) :=
  ClosedSubschemeStructure.reduced (closedSubset T)

/-- The vanishing ideal defining the reduced induced scheme on a locally closed subset. -/
@[stacks 0F2L "ideal of a locally closed reduction"]
abbrev ideal (T : LocallyCloseds X) :
    (ambientOpen T).toScheme.IdealSheafData :=
  (closedStructure T).ideal

/-- The defining ideal has the prescribed closed support in the ambient open. -/
@[stacks 0F2L "locally closed reduction ideal support"]
theorem support_ideal (T : LocallyCloseds X) :
    (ideal T).support = closedSubset T := sorry

/-- The reduced induced scheme on a locally closed subset. -/
@[stacks 0F2L "scheme on a locally closed subset"]
abbrev scheme (T : LocallyCloseds X) : Scheme.{u} :=
  (closedStructure T).subscheme

/-- The closed immersion into the ambient open subscheme. -/
@[stacks 0F2L "closed stage of a locally closed reduction"]
abbrev ιToAmbientOpen (T : LocallyCloseds X) :
    scheme T ⟶ (ambientOpen T).toScheme :=
  (closedStructure T).ι

/-- The closed stage has image equal to the prescribed closed subset. -/
@[stacks 0F2L, simp]
theorem range_ιToAmbientOpen (T : LocallyCloseds X) :
    Set.range (ιToAmbientOpen T) = closedSubset T := sorry

/-- The canonical immersion of the locally closed reduced induced scheme into `X`. -/
@[stacks 0F2L "locally closed reduction immersion"]
abbrev ι (T : LocallyCloseds X) : scheme T ⟶ X :=
  ιToAmbientOpen T ≫ (ambientOpen T).ι

/-- The locally closed induced scheme is reduced. -/
@[stacks 0F2L "locally closed reduction is reduced", instance]
instance scheme_isReduced (T : LocallyCloseds X) :
    IsReduced (scheme T) := sorry

/-- The canonical map of a locally closed induced scheme is an immersion. -/
@[stacks 0F2L "locally closed reduction immersion instance", instance]
instance ι_isImmersion (T : LocallyCloseds X) :
    IsImmersion (ι T) := sorry

/-- The canonical immersion has set-theoretic range exactly `T`. -/
@[stacks 0F2L, simp]
theorem range_ι (T : LocallyCloseds X) :
    Set.range (ι T) = T := sorry

end AlgebraicGeometry.Scheme.LocallyClosedReduction
