module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Ext
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper

/-!
# Finiteness of coherent derived Ext over a proper algebraic space

Over a Noetherian affine base, derived Ext from a bounded-above coherent object to a
bounded-below coherent object is a finite module in every integer degree.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open DerivedCategory.TStructure
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.DerivedExt

variable {A : Type u} [CommRing A]
variable {X : AlgebraicSpace (Spec (CommRingCat.of A))}

variable [IsNoetherianRing A]

/-- If `X` is proper over a Noetherian affine scheme, then the `A`-module of degree-`n`
derived extensions from a bounded-above complex with coherent cohomology to a bounded-below
complex with coherent cohomology is finite. -/
@[stacks 0D0T]
theorem finite
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) [Proper f]
    (K L : ModuleDerived X)
    (hK_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X)) K)
    (hK_boundedAbove :
      (t.minus : ObjectProperty (ModuleDerived X)) K)
    (hL_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X)) L)
    (hL_boundedBelow :
      (t.plus : ObjectProperty (ModuleDerived X)) L)
    (n : ℤ) :
    Module.Finite A (value f K L n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.DerivedExt
