module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Topology

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- For a proper flat finitely presented morphism with quasi-compact and quasi-separated
target, the structure sheaf is identified with the diagonal right adjoint applied to the
derived pullback of a right-adjoint image along the first projection. -/
theorem structureSheaf_isomorphic_diagonalAdjointFst
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace Y] [QuasiSeparatedSpace Y] [IsProper f] [Flat f]
    [Scheme.Hom.FinitePresentation f]
    (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh X)
    (c : Scheme.DerivedQCoh (CategoryTheory.Limits.pullback f f) ⥤
      Scheme.DerivedQCoh X)
    (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (cAdjunction : pushforwardCohomologyIn (pullback.diagonal f) ⊣ c) :
    IsIsomorphic (structureSheaf X)
      (c.obj ((pullback (pullback.fst f f)).obj (a.obj (structureSheaf Y)))) := sorry

/-- For a proper flat finitely presented morphism with quasi-compact and quasi-separated
target, the structure sheaf is identified with the diagonal right adjoint applied to the
derived pullback of a right-adjoint image along the second projection. -/
theorem structureSheaf_isomorphic_diagonalAdjointSnd
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace Y] [QuasiSeparatedSpace Y] [IsProper f] [Flat f]
    [Scheme.Hom.FinitePresentation f]
    (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh X)
    (c : Scheme.DerivedQCoh (CategoryTheory.Limits.pullback f f) ⥤
      Scheme.DerivedQCoh X)
    (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (cAdjunction : pushforwardCohomologyIn (pullback.diagonal f) ⊣ c) :
    IsIsomorphic (structureSheaf X)
      (c.obj ((pullback (pullback.snd f f)).obj (a.obj (structureSheaf Y)))) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
