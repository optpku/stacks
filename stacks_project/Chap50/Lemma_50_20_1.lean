/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.PoincareDuality.Hodge

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed TopologicalSpace
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

/- Lemma 50.20.1: a nonempty smooth proper equidimensional `k`-scheme of
dimension `d` admits a trace on its shifted top forms whose complementary Hodge
cup-product pairings are perfect. -/
@[stacks 0FW4] #check (AlgebraicGeometry.Scheme.DeRham.existsHodgePoincareTrace :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) (d : ℕ)
      [Nonempty X.left] [Smooth X.hom] [IsProper X.hom]
      [EquidimensionalSpace X.left]
      [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.left.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.TensorDescends X.left.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.IsLocalization X.left.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
        (Spec (CommRingCat.of k)).toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.TensorDescends
        (Spec (CommRingCat.of k)).toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.IsLocalization
        (Spec (CommRingCat.of k)).toRingedSpace]
      [HomotopyCategory.KFlat.HasResolutions X.left.Modules]
      [RingedSite.Hom.DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom X.hom.toShHom)]
      [Functor.Monoidal (RingedSpace.modulePullbackDerived X.hom.toShHom)]
      [MonoidalClosed
        (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)],
      topologicalKrullDim X.left = d →
        ∃ t : (AlgebraicGeometry.Scheme.DeRham.pushforwardForm X.hom d)⟦(d : ℤ)⟧ ⟶
            𝟙_ (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace),
          AlgebraicGeometry.Scheme.DeRham.PoincareTrace.IsPerfect X.hom d t)

/- Uniqueness of Hodge Poincaré traces: any two perfect traces on a nonempty
smooth proper equidimensional `k`-scheme of dimension `d` differ by
precomposition with a unit of `Γ(X.left, ⊤)`. -/
#check
  (AlgebraicGeometry.Scheme.DeRham.hodgePoincareTrace_unique :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) (d : ℕ)
      [Nonempty X.left] [Smooth X.hom] [IsProper X.hom]
      [EquidimensionalSpace X.left]
      [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.left.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.TensorDescends X.left.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.IsLocalization X.left.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
        (Spec (CommRingCat.of k)).toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.TensorDescends
        (Spec (CommRingCat.of k)).toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.IsLocalization
        (Spec (CommRingCat.of k)).toRingedSpace]
      [HomotopyCategory.KFlat.HasResolutions X.left.Modules]
      [RingedSite.Hom.DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom X.hom.toShHom)]
      [Functor.Monoidal (RingedSpace.modulePullbackDerived X.hom.toShHom)]
      [MonoidalClosed
        (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)],
      topologicalKrullDim X.left = d →
        ∀ t t' : (AlgebraicGeometry.Scheme.DeRham.pushforwardForm X.hom d)⟦(d : ℤ)⟧ ⟶
          𝟙_ (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace),
        AlgebraicGeometry.Scheme.DeRham.PoincareTrace.IsPerfect X.hom d t →
          AlgebraicGeometry.Scheme.DeRham.PoincareTrace.IsPerfect X.hom d t' →
          ∃ u : Γ(X.left, ⊤)ˣ,
            t' = AlgebraicGeometry.Scheme.DeRham.PoincareTrace.unitAction X.hom d u ≫ t)
