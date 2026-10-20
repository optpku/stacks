module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Effectivity
public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Etale

/-!
# Effective étale descent data

Effectivity of an étale descent datum is membership in the essential image of the
restricted étale canonical functor.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DescentData.Etale

/-- An étale descent datum is effective when it lies in the essential image of the
restricted étale canonical functor. -/
abbrev IsEffective {X S : Scheme.{u}} {f : X ⟶ S} (D : Etale f) : Prop :=
  (canonicalFunctor f).essImage D

/-- An étale descent datum is effective exactly when it is isomorphic to the canonical
datum of a scheme étale over the base. -/
theorem isEffective_iff {X S : Scheme.{u}} {f : X ⟶ S} (D : Etale f) :
    D.IsEffective ↔ ∃ U : S.Etale, Nonempty ((canonicalFunctor f).obj U ≅ D) := sorry

namespace IsEffective

/-- Every canonical étale descent datum is effective. -/
theorem ofObj {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Etale) :
    ((canonicalFunctor f).obj U).IsEffective := sorry

/-- Effectivity of étale descent data is preserved by isomorphism. -/
theorem ofIso {X S : Scheme.{u}} {f : X ⟶ S} {D E : Etale f}
    (e : D ≅ E) (hD : D.IsEffective) : E.IsEffective := sorry

/-- A datum effective through the restricted étale canonical functor is effective as an
ordinary scheme descent datum after forgetting étaleness. -/
theorem toUnderlying {X S : Scheme.{u}} {f : X ⟶ S} {D : Etale f}
    (hD : D.IsEffective) :
    AlgebraicGeometry.Scheme.DescentData.IsEffective D.obj := sorry

end IsEffective

end AlgebraicGeometry.Scheme.DescentData.Etale
