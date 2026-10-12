/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Length

/-!
# Length over an Artinian local ring

Over an Artinian local ring, composition length identifies the finite-module Grothendieck group
with `ℤ`.  This leaf keeps that local specialization beside the general length homomorphism.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.ModuleCat.K0

variable (R : Type u) [CommRing R] [IsArtinianRing R] [IsLocalRing R]

/-
API design: `finiteLength` remains the Artinian-general map.  Locality is introduced only for
its inverse: an integer is sent to that multiple of the residue-field class.  The explicit inverse
and both inverse laws make the resulting `AddEquiv` symmetric and keep consumers independent of
the chosen inverse hidden inside `AddEquiv.ofBijective`.  The source works in one universe; a
cross-universe statement would require a separate Grothendieck-group change-of-universe
comparison, so it is not asserted here.
-/

namespace Finite

/-- The class of the residue field in the finite-module Grothendieck group. -/
@[stacks 00JI "residue-field class in finite-module K0"]
def residueFieldClass : finite.{u, u} R :=
  finiteClass R (IsLocalRing.ResidueField R)

/-- The additive map sending an integer to that multiple of the residue-field class. -/
@[stacks 00JI "virtual residue-field classes in finite-module K0"]
def ofLength : ℤ →+ finite.{u, u} R :=
  zmultiplesHom _ (residueFieldClass R)

/-- The virtual residue-field class of length one is the residue-field class. -/
@[simp]
theorem ofLength_one : ofLength R 1 = residueFieldClass R := sorry

end Finite

/-- Composition length sends the residue-field class to `1`. -/
@[stacks 00JI "length of the residue-field class", simp]
theorem finiteLength_residueFieldClass :
    finiteLength R (Finite.residueFieldClass R) = 1 := sorry

/-- Taking length after forming a virtual residue-field class recovers the integer. -/
@[stacks 00JI "length of virtual residue-field classes", simp]
theorem finiteLength_ofLength (n : ℤ) :
    finiteLength R (Finite.ofLength R n) = n := sorry

namespace Finite

/-- The virtual residue-field class determined by the length of a finite-module class is that
class. -/
@[stacks 00JI "finite-module classes are determined by length", simp]
theorem ofLength_finiteLength (x : finite.{u, u} R) :
    ofLength R (finiteLength R x) = x := sorry

end Finite

/-- The explicit length identification of the finite-module Grothendieck group of an Artinian
local ring with `ℤ`. -/
@[stacks 00JI "local finite-module Grothendieck group length equivalence"]
def finiteLengthEquiv : finite.{u, u} R ≃+ ℤ where
  toFun := finiteLength R
  invFun := Finite.ofLength R
  left_inv := Finite.ofLength_finiteLength R
  right_inv := finiteLength_ofLength R
  map_add' := (finiteLength R).map_add

/-- Lemma 10.55.7 (Tag 00JI): over an Artinian local ring, the length map on the finite-module
Grothendieck group is an isomorphism. -/
@[stacks 00JI "length is an isomorphism on the local finite-module Grothendieck group"]
theorem finiteLength_bijective :
    Function.Bijective ((finiteLength R) : finite.{u, u} R → ℤ) := sorry

/-- The local length equivalence evaluates by the canonical length homomorphism. -/
@[stacks 00JI "local length equivalence evaluation", simp]
theorem finiteLengthEquiv_apply (x : finite.{u, u} R) :
    finiteLengthEquiv R x = finiteLength R x := sorry

/-- The inverse local length equivalence forms the corresponding virtual residue-field class. -/
@[stacks 00JI "inverse local length equivalence evaluation", simp]
theorem finiteLengthEquiv_symm_apply (n : ℤ) :
    (finiteLengthEquiv R).symm n = Finite.ofLength R n := sorry

end CategoryTheory.ModuleCat.K0
