/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Ext.Finite

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.TStructure

universe u

/- Lemma 36.11.7: if `X` is proper over a Noetherian ring `A`, then every
`A`-module `Ext⁽n⁾(K, L)` is finite when `K` has bounded-above coherent cohomology
and `L` has bounded-below coherent cohomology. -/
@[stacks 0D0D] #check
  (AlgebraicGeometry.Scheme.Hom.DerivedExt.finite :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
      (K L : RingedSpace.ModuleDerived X.toRingedSpace)
      (hK_coherent : DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) K)
      (hK_boundedAbove :
        (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) K)
      (hL_coherent : DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L)
      (hL_boundedBelow :
        (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) L)
      (n : ℤ),
      Module.Finite A (AlgebraicGeometry.Scheme.Hom.DerivedExt.value f K L n))
