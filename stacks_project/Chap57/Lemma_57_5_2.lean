/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.BoundedCoherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom
open DerivedCategory.TStructure
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/- Lemma 57.5.2: for a field `k`, a natural number `n`, and
`K : Scheme.DerivedQCoh (scheme k n)`, bounded coherent cohomology is equivalent
to finite total `k`-dimension after tensoring with every perfect object, after
derived Ext from every perfect object, and for the twists `twistingSheaf k n d`
with `d : Fin (n + 1)`. -/
@[stacks 0FYB]
#check (AlgebraicGeometry.ProjectiveSpace.boundedCoherent_tfae :
    ∀ (k : Type u) [Field k] (n : ℕ)
    (K : Scheme.DerivedQCoh (scheme k n)),
    List.TFAE [
      DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent (scheme k n).toRingedSpace.ringCatSheaf) K.obj ∧
        (t.bounded : ObjectProperty
          (RingedSpace.ModuleDerived (scheme k n).toRingedSpace)) K.obj,
      ∀ E : RingedSpace.ModuleDerived (scheme k n).toRingedSpace,
        RingedSpace.ModuleDerived.IsPerfect E →
          GradedObject.FiniteTotalDimension
            (fun i : ℤ ↦
              (DerivedCategory.homologyFunctor (ModuleCat k) i).obj
                ((Scheme.FlatPullbackSections.baseSections (toSpec k n)).obj
                  (E ⊗ᴸ K.obj))),
      ∀ E : RingedSpace.ModuleDerived (scheme k n).toRingedSpace,
        RingedSpace.ModuleDerived.IsPerfect E →
          GradedObject.FiniteTotalDimension
            (fun i : ℤ ↦
              DerivedExt.value (toSpec k n) E K.obj i),
      ∀ d : Fin (n + 1),
        GradedObject.FiniteTotalDimension
          (fun i : ℤ ↦
            (DerivedCategory.homologyFunctor (ModuleCat k) i).obj
              ((Scheme.FlatPullbackSections.baseSections (toSpec k n)).obj
                (K.obj ⊗ᴸ (DerivedCategory.singleFunctor (scheme k n).Modules 0).obj
                  (twistingSheaf k n (d : ℤ)))))
    ])

end AlgebraicGeometry.ProjectiveSpace

end
