/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.AffinePullback
public import stacks_project.Chap36.Lemma_36_3_8_Pullback

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- The compatibility import exposes the affine derived-pullback comparison with the
source-facing aliases. -/
#check (affinePullbackIso :
  ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B)
      [HasDerivedCategory.{u + 1} (RingedSpace.QCoh (Spec A).toRingedSpace)]
      [HasDerivedCategory.{u + 1} (RingedSpace.QCoh (Spec B).toRingedSpace)],
    ModuleCat.derivedExtensionOfScalars φ.hom ⋙ affineFunctor B ≅
      affineFunctor A ⋙ pullback (Spec.map φ))

end AlgebraicGeometry.Scheme.DerivedQCoh
