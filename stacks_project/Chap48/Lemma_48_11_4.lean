module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.Affine.BoundedBelow
public import stacks_project.Chap36.Lemma_36_5_4
public import stacks_project.Chap48.Lemma_48_3_5
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.Plus

noncomputable section

universe u

/- Lemma 48.11.4 (1): for a finite pseudo-coherent morphism, derived internal Hom
   gives a bounded-below quasi-coherent functor. -/
@[stacks 0AX2] #check (AlgebraicGeometry.Scheme.DerivedQCoh.derivedInternalHomPlus :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)
      [AlgebraicGeometry.IsFinite f] [AlgebraicGeometry.PseudoCoherent f],
      AlgebraicGeometry.Scheme.DerivedQCoh.Plus X ⥤
        AlgebraicGeometry.Scheme.DerivedQCoh.PushforwardQCohPlus f)

/- Lemma 48.11.4 (2): over a quasi-compact, quasi-separated target, the chosen
   bounded-below right adjoint followed by affine pushforward agrees with internal Hom. -/
@[stacks 0AX2] #check (AlgebraicGeometry.Scheme.DerivedQCoh.rightAdjointPlus_comp_affinePushforwardPlus_isomorphic :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)
      [AlgebraicGeometry.IsFinite f] [AlgebraicGeometry.PseudoCoherent f]
      [CompactSpace X] [QuasiSeparatedSpace X]
      (a : AlgebraicGeometry.Scheme.DerivedQCoh X ⥤
        AlgebraicGeometry.Scheme.DerivedQCoh Y)
      (adj : AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a),
      IsIsomorphic
        (AlgebraicGeometry.Scheme.DerivedQCoh.rightAdjointPlus f a adj ⋙
          AlgebraicGeometry.Scheme.DerivedQCoh.affinePushforwardToPushforwardStructurePlus f)
        (AlgebraicGeometry.Scheme.DerivedQCoh.derivedInternalHomPlus f))
