/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.ClosedImmersion.InternalHom

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- For a closed immersion between schemes separated and of finite type over a Noetherian
base, the canonical bounded-below right adjoint to derived pushforward is naturally isomorphic
to derived internal Hom from the structure sheaf of the source. -/
theorem closedImmersionUpperShriek_isomorphic_internalHom
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeSeparatedOver S} (i : X ⟶ Y)
    [IsClosedImmersion i.hom.left] :
    IsIsomorphic
      (rightAdjointPlus i.hom.left
        (pushforwardCohomologyIn i.hom.left).rightAdjoint
        (Adjunction.ofIsLeftAdjoint (pushforwardCohomologyIn i.hom.left)))
      (closedImmersionInternalHomPlus i.hom.left) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
