/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.J2.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Variety
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- The underlying scheme of a variety over a field is locally Noetherian. -/
noncomputable instance instIsLocallyNoetherianLeftOfVariety
    (X : SchemeOverField k) [Variety X] : IsLocallyNoetherian X.left := sorry

/-- The regular locus of a variety over a field is open. -/
theorem regularLocus_isOpen_of_variety (X : SchemeOverField k) [Variety X] :
    IsOpen X.left.regularLocus := sorry

/-- The regular locus of a variety over a field, regarded as its canonical open subscheme. -/
def regularOpen (X : SchemeOverField k) [Variety X] : X.left.Opens :=
  ⟨X.left.regularLocus, regularLocus_isOpen_of_variety X⟩

/-- Membership in the regular open means that the corresponding local ring is regular. -/
theorem mem_regularOpen (X : SchemeOverField k) [Variety X] (x : X.left) :
    x ∈ X.regularOpen ↔ IsRegularLocalRing (X.left.presheaf.stalk x) := sorry

/-- The regular open of a regular variety is the whole underlying scheme. -/
theorem regularOpen_eq_top (X : SchemeOverField k) [Variety X] [Scheme.Regular X.left] :
    X.regularOpen = ⊤ := sorry

end AlgebraicGeometry.SchemeOverField
