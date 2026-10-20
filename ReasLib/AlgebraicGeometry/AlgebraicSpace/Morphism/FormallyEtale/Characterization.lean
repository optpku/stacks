module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.Vanishing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyEtale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyUnramified.Differentials

/-!
# Characterizations of formally étale morphisms of algebraic spaces

Formal étaleness is characterized by triviality of the universal first-order
thickening, or by vanishing of the relative differentials and conormal sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FormallyEtale

/-- A morphism of algebraic spaces is formally étale if and only if it is
formally unramified and its identity is a universal first-order thickening
over the target. -/
theorem iff_isUniversalFirstOrder_id {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    FormallyEtale f ↔ FormallyUnramified f ∧ IsUniversalFirstOrder (𝟙 X) f :=
  sorry

/-- A morphism of algebraic spaces is formally étale if and only if it is
formally unramified and its conormal sheaf vanishes. -/
theorem iff_isZero_conormal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    FormallyEtale f ↔ FormallyUnramified f ∧ isZeroConormal f :=
  sorry

/-- A morphism of algebraic spaces is formally étale if and only if its sheaf
of relative differentials and its conormal sheaf both vanish. -/
theorem iff_isZero_relativeDifferentials_and_conormal {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    FormallyEtale f ↔ IsZero (Ω[f]) ∧ isZeroConormal f :=
  sorry

/-- A formally étale morphism of algebraic spaces is formally unramified. -/
instance toFormallyUnramified {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} [FormallyEtale f] :
    FormallyUnramified f :=
  sorry

/-- The identity morphism is a universal first-order thickening of a formally
étale morphism of algebraic spaces over the target. -/
instance instIsUniversalFirstOrder_id {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [FormallyEtale f] : IsUniversalFirstOrder (𝟙 X) f :=
  sorry

/-- A formally unramified morphism of algebraic spaces whose identity is a
universal first-order thickening over the target is formally étale. -/
instance of_isUniversalFirstOrder_id {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [FormallyUnramified f] [IsUniversalFirstOrder (𝟙 X) f] :
    FormallyEtale f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FormallyEtale
