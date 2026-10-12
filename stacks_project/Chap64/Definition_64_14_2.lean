/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap64.«64_14_3_1_Trace»
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local Lefschetz number

The sum of traces of geometric Frobenius on derived geometric stalks of a
complex of étale `Λ`-modules at `k`-rational points, valued in `Λ♮`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry MonoidalCategory Ring

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable {Λ : Type u} [CommRing Λ]
variable [HasColimitsOfSize.{u, u} (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {Y : Scheme.{u}},
    HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Definition 64.14.2. With `Λ`, `X`, `k`, `K` as in Definition 64.14.1.
Since `K` lies in `D_ctf(X, Λ)`, for any geometric point `x̄` of `X` the
complex `K_x̄` is perfect in `D_perf(Λ)`. The Frobenius `π_X` acts on
`K_x̄`. The local Lefschetz number of `K` is the sum
`∑_{x ∈ X(k)} Tr(π_x | K_x̄)`, again an element of `Λ♮`.
Here `X(k)` is the type `𝟙_ ⟶ X`, `K_x̄` is `geometricDerivedStalk K x`,
`π_x` is `geometricFrobeniusDerivedStalk K x`, stalkwise perfectness is
`DerivedCategory.IsPerfect` (as supplied by `isPerfect_geometricDerivedStalk`
when `K` is constructible of finite Tor-dimension), and the displayed sum is
`traceGeometricFrobeniusStalks`. -/
@[stacks 03TY]
noncomputable def localLefschetzNumber (X : SchemeOverField k)
    (K : EtaleDerived X.left Λ)
    (hK : ∀ x : (𝟙_ (SchemeOverField k) ⟶ X),
      DerivedCategory.IsPerfect (geometricDerivedStalk K x)) : Λ♮ :=
  traceGeometricFrobeniusStalks X K hK

/-- The local Lefschetz number equals the operational stalk-trace sum
`traceGeometricFrobeniusStalks`. -/
theorem localLefschetzNumber_eq (X : SchemeOverField k)
    (K : EtaleDerived X.left Λ)
    (hK : ∀ x : (𝟙_ (SchemeOverField k) ⟶ X),
      DerivedCategory.IsPerfect (geometricDerivedStalk K x)) :
    localLefschetzNumber X K hK = traceGeometricFrobeniusStalks X K hK :=
  sorry

/-- The local Lefschetz number is the finitely supported sum of traces of
geometric Frobenius on derived geometric stalks, valued in `Λ♮`. -/
theorem localLefschetzNumber_spec (X : SchemeOverField k)
    (K : EtaleDerived X.left Λ)
    (hK : ∀ x : (𝟙_ (SchemeOverField k) ⟶ X),
      DerivedCategory.IsPerfect (geometricDerivedStalk K x)) :
    localLefschetzNumber X K hK =
      ∑ᶠ x : (𝟙_ (SchemeOverField k) ⟶ X),
        (hK x).traceNatural (geometricFrobeniusDerivedStalk K x) :=
  sorry

end AlgebraicGeometry.SchemeOverField
