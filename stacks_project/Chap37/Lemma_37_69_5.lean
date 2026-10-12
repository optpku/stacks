/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.GlobalSections

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped CartesianClosed CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 37.69.5: if `f : X ⟶ Spec (CommRingCat.of A)` is separated and of finite
presentation, and derived global sections of `E ⊗ᴸ K` are pseudo-coherent over `A` for every
perfect `E`, then `K` is pseudo-coherent relative to `A`. -/
@[stacks 0GES] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.isPseudoCoherentOver_of_globalSectionsTensor_perfect :
    ∀ {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f]
    [Scheme.Hom.FinitePresentation f] (K : DerivedQCoh X)
    (hperfect : ∀ E : RingedSpace.ModuleDerived X.toRingedSpace,
      RingedSpace.ModuleDerived.IsPerfect E →
        DerivedCategory.IsPseudoCoherent
          ((Scheme.FlatPullbackSections.baseSections f).obj (E ⊗ᴸ K.obj))),
    Scheme.ModuleDerived.IsPseudoCoherentOver f K.obj)

end AlgebraicGeometry.Scheme.DerivedQCoh
