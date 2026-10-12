/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Ext
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Coherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.RHom.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finiteness of derived Ext over an affine base

Derived extensions from a bounded-above coherent complex to a bounded-below coherent complex on a
proper scheme form finite modules over the Noetherian affine base.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.TStructure

universe u

namespace AlgebraicGeometry.Scheme.Hom.DerivedExt

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {X : Scheme.{u}}

/-- If `X` is proper over a Noetherian affine scheme, then the `A`-module of degree-`n`
derived extensions from a bounded-above complex with coherent cohomology to a bounded-below
complex with coherent cohomology is finite. -/
@[stacks 0D0D "finiteness of coherent derived Ext over a proper affine base"]
theorem finite (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (K L : RingedSpace.ModuleDerived X.toRingedSpace)
    (hK_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) K)
    (hK_boundedAbove :
      (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) K)
    (hL_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L)
    (hL_boundedBelow :
      (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) L)
    (n : ℤ) :
    Module.Finite A (value f K L n) := sorry

end AlgebraicGeometry.Scheme.Hom.DerivedExt
