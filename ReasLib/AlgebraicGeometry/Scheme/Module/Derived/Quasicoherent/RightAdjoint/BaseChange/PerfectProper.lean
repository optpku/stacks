module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint.BaseChange.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.OpenRestriction

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- For a Tor-independent cartesian square over Noetherian schemes with perfect proper
vertical map, the canonical right-adjoint base-change comparison is an isomorphism on
every unbounded quasi-coherent complex. -/
theorem rightAdjoint_baseChangeComparison_isIso_of_perfect_proper
    {X' X Y' Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y'] [IsNoetherian Y]
    [CompactSpace X'] [QuasiSeparatedSpace X']
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsProper f] [LocallyOfType RingHom.IsPerfectRingMap f]
    (sq : IsPullback g' f' f g)
    (hTor : Scheme.TorIndependentOver (Over.mk f) (Over.mk g))
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (K : DerivedQCoh Y) :
    let dualBaseChangeIso :=
      @asIso _ _ _ _
        (BaseChange.rightMate g' f' f g sq.toCommSq a a' fAdj f'Adj)
        (BaseChange.rightMate_isIso_of_torIndependent
          g' f' f g sq a a' fAdj f'Adj hTor)
    IsIso
      ((DerivedBaseChange.mapOfRight
        (pullbackPushforwardAdjunction g) (pullbackPushforwardAdjunction g')
        dualBaseChangeIso.inv).app K) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
