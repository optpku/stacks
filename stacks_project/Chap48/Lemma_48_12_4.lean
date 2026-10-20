module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint.BaseChange.ProperFlat
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 48.12.4: let `g : Y' ⟶ Y` be a morphism of quasi-compact and
quasi-separated schemes and let `f : X ⟶ Y` be proper, flat, and of finite
presentation. Then the base-change map (48.5.0.1) is an isomorphism for every
`K : DerivedQCoh Y`. -/
@[stacks 0AAB] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.mapOfRight_app_isIso_of_proper_flat :
    ∀ {X Y' Y : Scheme.{u}}
      [CompactSpace Y'] [QuasiSeparatedSpace Y']
      [CompactSpace Y] [QuasiSeparatedSpace Y]
      (f : X ⟶ Y) (g : Y' ⟶ Y)
      [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X)
      (a' : DerivedQCoh Y' ⥤ DerivedQCoh (CategoryTheory.Limits.pullback f g))
      (fAdj : pushforwardCohomologyIn f ⊣ a)
      (f'Adj : pushforwardCohomologyIn (CategoryTheory.Limits.pullback.snd f g) ⊣ a')
      (K : DerivedQCoh Y),
      IsIso
        ((DerivedBaseChange.mapOfRight
          (pullbackPushforwardAdjunction g)
          (pullbackPushforwardAdjunction (CategoryTheory.Limits.pullback.fst f g))
          (rightMateIsoOfFlatLeft f g a a' fAdj f'Adj).inv).app K))

end AlgebraicGeometry.Scheme.DerivedQCoh
