/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.DerivedPushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.StructureSheaf.FiniteEtale

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.DerivedPushforward

/-- For a proper smooth family with nonempty fibres, the degree-zero relative
differential becomes zero after applying the coefficient pushforward. -/
theorem pushforward_relativeDifferential_zero
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsProper f] [Smooth f]
    [Scheme.Hom.RelativeDimension f n]
    (h_nonempty : ∀ s : S, Nonempty (f.fiber s)) :
    (RingedSite.Hom.modulePushforward (pushforwardHom f)).map
        (RingedSpace.DeRham.d f.toLRSHom.toShHom 0) = 0 := sorry

end AlgebraicGeometry.Scheme.DeRham.DerivedPushforward
