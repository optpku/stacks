module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.PoincareDuality.Forms

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed TopologicalSpace
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

/- Lemma 50.24.3 (1): in Situation 50.24.1, there exists a trace on the shifted
top relative forms whose complementary-degree cup-product pairings are perfect. -/
@[stacks 0G8I] #check
  (AlgebraicGeometry.Scheme.DeRham.existsPoincareTrace :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
      [CompactSpace S] [QuasiSeparatedSpace S] [IsProper f] [Smooth f]
      [Scheme.Hom.RelativeDimension f n]
      [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends S.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.TensorDescends S.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.IsLocalization S.toRingedSpace]
      [HomotopyCategory.KFlat.HasResolutions X.Modules]
      [RingedSite.Hom.DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom f.toShHom)]
      [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
      [MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)],
      (∀ s : S, Nonempty (f.fiber s)) →
        ∃ t : (AlgebraicGeometry.Scheme.DeRham.pushforwardForm f n)⟦(n : ℤ)⟧ ⟶
            𝟙_ (RingedSpace.ModuleDerived S.toRingedSpace),
          AlgebraicGeometry.Scheme.DeRham.PoincareTrace.IsPerfect f n t)

/- Lemma 50.24.3 (2): any two perfect traces differ by precomposition with
multiplication by a unit of `Γ(X, ⊤)`. -/
@[stacks 0G8I] #check
  (AlgebraicGeometry.Scheme.DeRham.poincareTrace_unique :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
      [CompactSpace S] [QuasiSeparatedSpace S] [IsProper f] [Smooth f]
      [Scheme.Hom.RelativeDimension f n]
      [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends S.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.TensorDescends S.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.IsLocalization S.toRingedSpace]
      [HomotopyCategory.KFlat.HasResolutions X.Modules]
      [RingedSite.Hom.DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom f.toShHom)]
      [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
      [MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)],
      (∀ s : S, Nonempty (f.fiber s)) →
        ∀ t t' : (AlgebraicGeometry.Scheme.DeRham.pushforwardForm f n)⟦(n : ℤ)⟧ ⟶
          𝟙_ (RingedSpace.ModuleDerived S.toRingedSpace),
        AlgebraicGeometry.Scheme.DeRham.PoincareTrace.IsPerfect f n t →
          AlgebraicGeometry.Scheme.DeRham.PoincareTrace.IsPerfect f n t' →
          ∃ u : Γ(X, ⊤)ˣ,
            t' = AlgebraicGeometry.Scheme.DeRham.PoincareTrace.unitAction f n u ≫ t)
