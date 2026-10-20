module

public import ReasLib.AlgebraicGeometry.Scheme.Characteristic.Prime

/-!
# Characteristic along scheme morphisms

This leaf records that the sectionwise characteristic of a target scheme is
inherited by the source of a scheme morphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- If every section of the structure sheaf of the target has characteristic `p`, then the same
holds for every section of the source. -/
theorem charP_opens_of_target {p : ℕ} {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ U : S.Opens, CharP (Γ(S, U)) p] :
    ∀ U : X.Opens, CharP (Γ(X, U)) p := sorry

/-- A morphism to a scheme of characteristic `p` gives its source scheme characteristic `p`. -/
theorem isCharP_of_target {p : ℕ} {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.IsCharP S p] : Scheme.IsCharP X p := sorry

end AlgebraicGeometry.Scheme.Hom
