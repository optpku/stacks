/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RelativeDualizing.Rigidity
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Duality.Rigidity
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.DerivedQCoh
open CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 48.12.8 (Rigidity) (1): for a proper flat morphism of finite presentation
`f : X ⟶ Y`, with `Y` quasi-compact and quasi-separated, `𝒪_X` is canonically
isomorphic to the diagonal right adjoint applied to the pullback of `ω_{X/Y}` along
the first projection `X ×[Y] X ⟶ X`. -/
@[stacks 0E2P] #check
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

/- Lemma 48.12.8 (Rigidity) (2): under the same hypotheses, `𝒪_X` is canonically
isomorphic to the diagonal right adjoint applied to the pullback of `ω_{X/Y}` along
the second projection `X ×[Y] X ⟶ X`. -/
@[stacks 0E2P] #check
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

/- Lemma 48.12.8 (Rigidity) (3): under the same hypotheses, `ω_{X/Y}` is canonically
isomorphic to the diagonal right adjoint applied to the derived tensor product of its
pullbacks along the two projections `X ×[Y] X ⟶ X`. -/
@[stacks 0E2P] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.relativeDualizingComplexIso :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [CompactSpace Y] [QuasiSeparatedSpace Y] [IsProper f] [Flat f]
      [Scheme.Hom.FinitePresentation f]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X)
      (c : DerivedQCoh (CategoryTheory.Limits.pullback f f) ⥤ DerivedQCoh X)
      (aAdjunction : pushforwardCohomologyIn f ⊣ a)
      (cAdjunction : pushforwardCohomologyIn
        (CategoryTheory.Limits.pullback.diagonal f) ⊣ c),
      IsIsomorphic (a.obj (structureSheaf Y))
        (c.obj (tensorObj
          ((AlgebraicGeometry.Scheme.DerivedQCoh.pullback
            (CategoryTheory.Limits.pullback.fst f f)).obj
            (a.obj (structureSheaf Y)))
          ((AlgebraicGeometry.Scheme.DerivedQCoh.pullback
            (CategoryTheory.Limits.pullback.snd f f)).obj
            (a.obj (structureSheaf Y))))))
