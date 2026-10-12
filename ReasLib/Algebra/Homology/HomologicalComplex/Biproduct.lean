/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Binary Biproducts of Homological Complexes

Binary biproducts lift pointwise from a preadditive category to homological complexes of any
shape.  Registering this canonical construction once also covers iterated complexes, including
double complexes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace HomologicalComplex

variable (C : Type u) [Category.{v} C] [Preadditive C]
  {ι : Type w} (c : ComplexShape ι)

/-- Binary biproducts of homological complexes are computed pointwise. -/
@[stacks 0G6D "pointwise binary biproducts of homological complexes"]
instance instHasBinaryBiproducts [HasBinaryBiproducts C] :
    HasBinaryBiproducts (HomologicalComplex C c) := sorry


end HomologicalComplex

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {ι : Type w} {c : ComplexShape ι}
variable (K L : HomologicalComplex C c)
variable [∀ i, HasBinaryBiproduct (K.X i) (L.X i)]

/-- Under the pointwise biproduct identification, the differential of a binary biproduct complex
is the biproduct of the two differentials. -/
@[stacks 0G6D "biproduct differential in pointwise coordinates"]
theorem biprodXIso_d
    (p q : ι) :
    (biprod K L).d p q ≫ (biprodXIso K L q).hom =
      (biprodXIso K L p).hom ≫ biprod.map (K.d p q) (L.d p q) := sorry

/-- The inverse pointwise biproduct comparison sends the chain-level first projection to the
objectwise first projection.  This is the inverse orientation of Mathlib's
`HomologicalComplex.biprodXIso_hom_fst`, exposed here because it is the convenient normal form
for componentwise chain calculations. -/
@[reassoc (attr := simp), stacks 0G6D "inverse pointwise biproduct first projection"]
theorem biprodXIso_inv_fst
    (i : ι) :
    (biprodXIso K L i).inv ≫
        (biprod.fst : biprod K L ⟶ K).f i =
      (biprod.fst : (K.X i) ⊞ (L.X i) ⟶ K.X i) := sorry

/-- The inverse pointwise biproduct comparison sends the chain-level second projection to the
objectwise second projection. -/
@[reassoc (attr := simp), stacks 0G6D "inverse pointwise biproduct second projection"]
theorem biprodXIso_inv_snd
    (i : ι) :
    (biprodXIso K L i).inv ≫
        (biprod.snd : biprod K L ⟶ L).f i =
      (biprod.snd : (K.X i) ⊞ (L.X i) ⟶ L.X i) := sorry

end HomologicalComplex
