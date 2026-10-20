module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.BaseChange.RightAdjoint
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Topology
public import ReasLib.AlgebraicGeometry.Scheme.TorIndependence.Flat

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- Flatness of the first scheme over the base canonically identifies the right-adjoint
base-change mate of the pullback square as a natural isomorphism. -/
noncomputable def rightMateIsoOfFlatLeft
    {X Y' Y : Scheme.{u}}
    [CompactSpace Y'] [QuasiSeparatedSpace Y']
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) (g : Y' ⟶ Y) [Flat f] [Scheme.Hom.FinitePresentation f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (a' : DerivedQCoh Y' ⥤ DerivedQCoh (CategoryTheory.Limits.pullback f g))
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn (CategoryTheory.Limits.pullback.snd f g) ⊣ a') :
    a' ⋙ pushforwardCohomologyIn (CategoryTheory.Limits.pullback.fst f g) ≅
      pushforwardCohomologyIn g ⋙ a :=
  @asIso _ _ _ _
    (@BaseChange.rightMate
      (CategoryTheory.Limits.pullback f g) X Y' Y
      (CategoryTheory.Limits.pullback.fst f g) (CategoryTheory.Limits.pullback.snd f g) f g
      (inferInstance : QuasiCompact f) (inferInstance : QuasiSeparated f)
      (inferInstance : QuasiCompact (CategoryTheory.Limits.pullback.snd f g))
      (inferInstance : QuasiSeparated (CategoryTheory.Limits.pullback.snd f g))
      (inferInstance : QuasiCompact g) (inferInstance : QuasiSeparated g)
      (inferInstance : QuasiCompact (CategoryTheory.Limits.pullback.fst f g))
      (inferInstance : QuasiSeparated (CategoryTheory.Limits.pullback.fst f g))
      (CategoryTheory.IsPullback.of_hasPullback f g).toCommSq a a' fAdj f'Adj)
    (@BaseChange.rightMate_isIso_of_torIndependent
      (CategoryTheory.Limits.pullback f g) X Y' Y
      (Scheme.Hom.compactSpace_of_finitePresentation (CategoryTheory.Limits.pullback.snd f g))
      (Scheme.Hom.quasiSeparatedSpace_of_finitePresentation
        (CategoryTheory.Limits.pullback.snd f g))
      (Scheme.Hom.compactSpace_of_finitePresentation f)
      (Scheme.Hom.quasiSeparatedSpace_of_finitePresentation f)
      (inferInstance : CompactSpace Y') (inferInstance : QuasiSeparatedSpace Y')
      (inferInstance : CompactSpace Y) (inferInstance : QuasiSeparatedSpace Y)
      (CategoryTheory.Limits.pullback.fst f g) (CategoryTheory.Limits.pullback.snd f g) f g
      (CategoryTheory.IsPullback.of_hasPullback f g)
      a a' fAdj f'Adj (TorIndependentOver.of_flat_left f g))

end AlgebraicGeometry.Scheme.DerivedQCoh
