/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Limit.Invertible
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Galois
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Continuity of Galois actions on Picard groups

The canonical Galois action on the Picard group after base change is continuous when the
Picard group has the discrete topology.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped MonoidalCategory

universe u

namespace AlgebraicGeometry.FieldExtension

/-- If a quasi-compact and quasi-separated `k`-scheme `X` has
`k ≃ Γ(X, 𝒪_X)` and a `k`-rational point, then the Galois action on the Picard group after
base change is continuous for the Krull topology on `Gal(K/k)` and the discrete topology on
the Picard group. -/
@[stacks 0CDT]
theorem continuous_picardAction
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (X : SchemeOverField k) [CompactSpace X.left.carrier]
    [QuasiSeparatedSpace X.left.carrier]
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_point : Nonempty (𝟙_ (SchemeOverField k) ⟶ X)) :
    Continuous (Picard.galoisActionMap k K X.hom) := sorry

end AlgebraicGeometry.FieldExtension
