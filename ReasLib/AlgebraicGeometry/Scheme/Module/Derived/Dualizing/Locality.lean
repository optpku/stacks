/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Koszul.PrincipalOpen
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Intrinsic
public import Mathlib.AlgebraicGeometry.Noetherian

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.ModuleDerived.Koszul

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A derived `𝒪_X`-module restricts to an intrinsic dualizing complex on the affine open `U`
when its pullback to `Spec Γ(X, U)` is isomorphic to an intrinsic dualizing complex. -/
def IsDualizingOnAffine {X : Scheme.{u}} [IsLocallyNoetherian X]
    (K : RingedSpace.ModuleDerived X.toRingedSpace) (U : X.affineOpens) : Prop :=
  ∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, U)),
    @DerivedCategory.IsDualizing Γ(X, U) inferInstance
      (IsLocallyNoetherian.component_noetherian U) ω ∧
      IsIsomorphic
        ((RingedSpace.modulePullbackDerived U.2.fromSpec.toShHom).obj K)
        ((affineDerivedTilde Γ(X, U)).obj ω)

/-- A derived `𝒪_X`-module on a locally Noetherian scheme is a dualizing complex when it is
dualizing on every affine open. -/
def IsDualizingComplex {X : Scheme.{u}} [IsLocallyNoetherian X]
    (K : RingedSpace.ModuleDerived X.toRingedSpace) : Prop :=
  ∀ U : X.affineOpens, IsDualizingOnAffine K U

/-- For a locally Noetherian scheme, affine-local dualizingness is equivalent to dualizingness on
the members of an affine open covering. -/
theorem isDualizingOnAffine_iff_exists_cover {X : Scheme.{u}} [IsLocallyNoetherian X]
    (K : RingedSpace.ModuleDerived X.toRingedSpace) :
    (∀ U : X.affineOpens, IsDualizingOnAffine K U) ↔
      ∃ (ι : Type u) (U : ι → X.affineOpens),
        (⨆ i, (U i : X.Opens)) = ⊤ ∧ ∀ i, IsDualizingOnAffine K (U i) := sorry

end AlgebraicGeometry.Scheme
