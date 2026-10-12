/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.TensorProduct
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.DerivedCategory.LocalCohomology

/- Lemma 47.9.5 (1): local cohomology of a derived tensor product is isomorphic
to tensoring the first factor with the local cohomology of the second. -/
@[stacks 0ALY] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.tensorObjIsoRight :
    ∀ {A : Type u} [CommRing A] (I : Ideal A), I.FG →
      ∀ (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I),
        (IdealPowerTorsion.inclusion I ⊣ RΓ) →
          ∀ K L : DerivedCategory (ModuleCat A),
            Nonempty
              ((RΓ.obj (DerivedTensor.Right.obj K L)).obj ≅
                DerivedTensor.Right.obj K (RΓ.obj L).obj))

/- Lemma 47.9.5 (2): local cohomology of a derived tensor product is isomorphic
to tensoring the local cohomology of the first factor with the second. -/
@[stacks 0ALY] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.tensorObjIsoLeft :
    ∀ {A : Type u} [CommRing A] (I : Ideal A), I.FG →
      ∀ (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I),
        (IdealPowerTorsion.inclusion I ⊣ RΓ) →
          ∀ K L : DerivedCategory (ModuleCat A),
            Nonempty
              ((RΓ.obj (DerivedTensor.Right.obj K L)).obj ≅
                DerivedTensor.Right.obj (RΓ.obj K).obj L))

/- Lemma 47.9.5 (3): applying local cohomology to both factors before taking
their derived tensor product does not change the local cohomology of the product. -/
@[stacks 0ALY] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.tensorObjIsoBoth :
    ∀ {A : Type u} [CommRing A] (I : Ideal A), I.FG →
      ∀ (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I),
        (IdealPowerTorsion.inclusion I ⊣ RΓ) →
          ∀ K L : DerivedCategory (ModuleCat A),
            Nonempty
              ((RΓ.obj (DerivedTensor.Right.obj K L)).obj ≅
                DerivedTensor.Right.obj (RΓ.obj K).obj (RΓ.obj L).obj))

/- Lemma 47.9.5 (4): if either factor has `I`-power-torsion cohomology, then
their derived tensor product also has `I`-power-torsion cohomology. -/
@[stacks 0ALY] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.tensor_mem :
    ∀ {A : Type u} [CommRing A] (I : Ideal A), I.FG →
      ∀ K L : DerivedCategory (ModuleCat A),
        (cohomologyIn (ModuleCat.isIdealPowerTorsion I) K ∨
          cohomologyIn (ModuleCat.isIdealPowerTorsion I) L) →
            cohomologyIn (ModuleCat.isIdealPowerTorsion I)
              (DerivedTensor.Right.obj K L))

end CategoryTheory.DerivedCategory.LocalCohomology
