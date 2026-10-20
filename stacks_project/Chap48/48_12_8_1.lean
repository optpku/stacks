module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RelativeDualizing.Rigidity
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

/- 48.12.8.1 (1) -/
@[stacks 0E2Q] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.structureSheaf_isomorphic_diagonalAdjointFst :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [CompactSpace Y] [QuasiSeparatedSpace Y] [IsProper f] [Flat f]
      [Scheme.Hom.FinitePresentation f]
      (a : AlgebraicGeometry.Scheme.DerivedQCoh Y ⥤
        AlgebraicGeometry.Scheme.DerivedQCoh X)
      (c : AlgebraicGeometry.Scheme.DerivedQCoh
        (CategoryTheory.Limits.pullback f f) ⥤
          AlgebraicGeometry.Scheme.DerivedQCoh X)
      (aAdjunction : AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a)
      (cAdjunction : AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn
        (CategoryTheory.Limits.pullback.diagonal f) ⊣ c),
      CategoryTheory.IsIsomorphic
        (AlgebraicGeometry.Scheme.DerivedQCoh.structureSheaf X)
        (c.obj ((AlgebraicGeometry.Scheme.DerivedQCoh.pullback
          (CategoryTheory.Limits.pullback.fst f f)).obj
          (a.obj (AlgebraicGeometry.Scheme.DerivedQCoh.structureSheaf Y)))))

/- 48.12.8.1 (2) -/
@[stacks 0E2Q] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.structureSheaf_isomorphic_diagonalAdjointSnd :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [CompactSpace Y] [QuasiSeparatedSpace Y] [IsProper f] [Flat f]
      [Scheme.Hom.FinitePresentation f]
      (a : AlgebraicGeometry.Scheme.DerivedQCoh Y ⥤
        AlgebraicGeometry.Scheme.DerivedQCoh X)
      (c : AlgebraicGeometry.Scheme.DerivedQCoh
        (CategoryTheory.Limits.pullback f f) ⥤
          AlgebraicGeometry.Scheme.DerivedQCoh X)
      (aAdjunction : AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a)
      (cAdjunction : AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn
        (CategoryTheory.Limits.pullback.diagonal f) ⊣ c),
      CategoryTheory.IsIsomorphic
        (AlgebraicGeometry.Scheme.DerivedQCoh.structureSheaf X)
        (c.obj ((AlgebraicGeometry.Scheme.DerivedQCoh.pullback
          (CategoryTheory.Limits.pullback.snd f f)).obj
          (a.obj (AlgebraicGeometry.Scheme.DerivedQCoh.structureSheaf Y)))))
