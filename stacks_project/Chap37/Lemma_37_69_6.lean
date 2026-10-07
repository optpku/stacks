module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative.GlobalSections

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped CartesianClosed CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 37.69.6: for a separated, finitely presented, flat morphism
`f : X ⟶ Spec (CommRingCat.of A)`, if `RΓ(X, E ⊗ᴸ K)` is perfect over `A` for every
perfect `E`, then `K` is perfect relative to `Spec A`. -/
@[stacks 0GET] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.isPerfectOver_of_globalSectionsTensor :
    {A : Type u} → [CommRing A] → {X : Scheme.{u}} →
      (f : X ⟶ Spec (CommRingCat.of A)) → [IsSeparated f] →
      [Scheme.Hom.FinitePresentation f] → [Flat f] → (K : DerivedQCoh X) →
      (∀ E : RingedSpace.ModuleDerived X.toRingedSpace,
        RingedSpace.ModuleDerived.IsPerfect E →
          DerivedCategory.IsPerfect
            ((Scheme.FlatPullbackSections.baseSections f).obj (E ⊗ᴸ K.obj))) →
        RingedSpace.ModuleDerived.IsPerfectOver f.toShHom K.obj)

end AlgebraicGeometry.Scheme.DerivedQCoh
