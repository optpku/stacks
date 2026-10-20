module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.Adjunction

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport

/-- A morphism of compactifications of the same morphism induces an isomorphism
between the associated compactly supported derived pushforward functors. -/
theorem compactSupportPushforward_iso_of_hom
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    {P Q : Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left)}
    (g : P ⟶ Q) :
    IsIsomorphic (compactSupportPushforward f P) (compactSupportPushforward f Q) := sorry

/-- Compactly supported derived pushforward along a finite-type separated morphism
is independent, up to isomorphism, of the choice of compactification. -/
theorem compactSupportPushforward_independent
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P Q : Compactification.Of (Over.left Y.obj) (Over.mk f.hom.left)) :
    IsIsomorphic (compactSupportPushforward f P) (compactSupportPushforward f Q) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport
