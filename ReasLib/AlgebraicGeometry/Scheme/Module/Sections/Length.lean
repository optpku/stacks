/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import Mathlib.RingTheory.Length

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The integer length defect of a morphism on global sections over an affine base,
given by the cokernel length minus the kernel length, with lengths converted to
natural numbers. -/
def sectionLengthDefect {A : Type u} [CommRing A] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of A)) {M N : Y.Modules} (g : M ⟶ N) : ℤ :=
  let linearMap := (p.globalSectionsFunctor.map g).hom
  ((Module.length A (p.globalSectionsMod N ⧸ linearMap.range)).toNat : ℤ) -
    ((Module.length A linearMap.ker).toNat : ℤ)

end AlgebraicGeometry.Scheme.Modules
