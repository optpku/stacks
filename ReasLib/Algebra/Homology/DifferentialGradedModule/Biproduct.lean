module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Preadditive

/-!
# Binary Biproducts of Differential Graded Modules

Right differential graded modules over a fixed differential graded algebra have canonical
binary biproducts, computed degreewise on products of modules.  This leaf keeps the concrete
object and its coordinate maps visible before registering the corresponding categorical
instance.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra R}

/-- The componentwise right action on the product of two differential graded modules. -/
@[stacks 09JJ "componentwise action on a binary DG-module biproduct"]
def biproductSmul (M N : DifferentialGradedModule.{u, v} A) (p i : ℤ) :
    (M.X p × N.X p) →ₗ[R] A.X i →ₗ[R] (M.X (p + i) × N.X (p + i)) where
  toFun x := (M.smul p i x.1).prod (N.smul p i x.2)
  map_add' := sorry
  map_smul' := sorry

/-- The canonical degreewise product of two right differential graded modules. -/
@[stacks 09JJ "explicit binary biproduct of differential graded modules"]
def biproduct (M N : DifferentialGradedModule.{u, v} A) :
    DifferentialGradedModule A where
  X n := ModuleCat.of R (M.X n × N.X n)
  d n := (M.d n).prodMap (N.d n)
  smul := biproductSmul M N
  d_sq := sorry
  smul_one := sorry
  smul_mul := sorry
  comm_d := sorry

/-- The degree-`n` term of the explicit biproduct is the product of the degree-`n` terms. -/
@[simp, stacks 09JJ "terms of an explicit DG-module biproduct"]
theorem biproduct_X (M N : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (biproduct M N).X n = ModuleCat.of R (M.X n × N.X n) := sorry

/-- The differential of the explicit biproduct is componentwise. -/
@[simp, stacks 09JJ "differential of an explicit DG-module biproduct"]
theorem biproduct_d (M N : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (biproduct M N).d n = (M.d n).prodMap (N.d n) := sorry

/-- The right action on the explicit biproduct is componentwise. -/
@[simp, stacks 09JJ "action on an explicit DG-module biproduct"]
theorem biproduct_smul (M N : DifferentialGradedModule.{u, v} A) (p i : ℤ) :
    (biproduct M N).smul p i = biproductSmul M N p i := sorry

namespace Biprod

/-- The first projection from the explicit biproduct of differential graded modules. -/
@[stacks 09JJ "first projection from an explicit DG-module biproduct"]
def fst (M N : DifferentialGradedModule.{u, v} A) : biproduct M N ⟶ M where
  hom n := LinearMap.fst R (M.X n) (N.X n)
  comm_d := sorry
  comm_smul := sorry

/-- The second projection from the explicit biproduct of differential graded modules. -/
@[stacks 09JJ "second projection from an explicit DG-module biproduct"]
def snd (M N : DifferentialGradedModule.{u, v} A) : biproduct M N ⟶ N where
  hom n := LinearMap.snd R (M.X n) (N.X n)
  comm_d := sorry
  comm_smul := sorry

/-- The first inclusion into the explicit biproduct of differential graded modules. -/
@[stacks 09JJ "first inclusion into an explicit DG-module biproduct"]
def inl (M N : DifferentialGradedModule.{u, v} A) : M ⟶ biproduct M N where
  hom n := LinearMap.inl R (M.X n) (N.X n)
  comm_d := sorry
  comm_smul := sorry

/-- The second inclusion into the explicit biproduct of differential graded modules. -/
@[stacks 09JJ "second inclusion into an explicit DG-module biproduct"]
def inr (M N : DifferentialGradedModule.{u, v} A) : N ⟶ biproduct M N where
  hom n := LinearMap.inr R (M.X n) (N.X n)
  comm_d := sorry
  comm_smul := sorry

/-- The universal map into the explicit biproduct. -/
@[stacks 09JJ "lift into an explicit DG-module biproduct"]
def lift {P M N : DifferentialGradedModule.{u, v} A} (f : P ⟶ M) (g : P ⟶ N) :
    P ⟶ biproduct M N where
  hom n := (f.hom n).prod (g.hom n)
  comm_d := sorry
  comm_smul := sorry

/-- The universal map out of the explicit biproduct. -/
@[stacks 09JJ "descent from an explicit DG-module biproduct"]
def desc {M N P : DifferentialGradedModule.{u, v} A} (f : M ⟶ P) (g : N ⟶ P) :
    biproduct M N ⟶ P where
  hom n := (f.hom n).coprod (g.hom n)
  comm_d := sorry
  comm_smul := sorry

/-- The componentwise map between explicit biproducts. -/
@[stacks 09JJ "componentwise map of explicit DG-module biproducts"]
def map {M N M' N' : DifferentialGradedModule.{u, v} A} (f : M ⟶ M') (g : N ⟶ N') :
    biproduct M N ⟶ biproduct M' N' where
  hom n := (f.hom n).prodMap (g.hom n)
  comm_d := sorry
  comm_smul := sorry

/-- The first projection is the first coordinate linear map in every degree. -/
@[simp, stacks 09JJ "first projection coordinates of an explicit DG-module biproduct"]
theorem fst_hom (M N : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (fst M N).hom n = LinearMap.fst R (M.X n) (N.X n) := sorry

/-- The second projection is the second coordinate linear map in every degree. -/
@[simp, stacks 09JJ "second projection coordinates of an explicit DG-module biproduct"]
theorem snd_hom (M N : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (snd M N).hom n = LinearMap.snd R (M.X n) (N.X n) := sorry

/-- The first inclusion is the first coordinate inclusion in every degree. -/
@[simp, stacks 09JJ "first inclusion coordinates of an explicit DG-module biproduct"]
theorem inl_hom (M N : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (inl M N).hom n = LinearMap.inl R (M.X n) (N.X n) := sorry

/-- The second inclusion is the second coordinate inclusion in every degree. -/
@[simp, stacks 09JJ "second inclusion coordinates of an explicit DG-module biproduct"]
theorem inr_hom (M N : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (inr M N).hom n = LinearMap.inr R (M.X n) (N.X n) := sorry

/-- The universal map into a biproduct is computed by pairing its components. -/
@[simp, stacks 09JJ "coordinate formula for a biproduct lift"]
theorem lift_hom {P M N : DifferentialGradedModule.{u, v} A}
    (f : P ⟶ M) (g : P ⟶ N) (n : ℤ) :
    (lift f g).hom n = (f.hom n).prod (g.hom n) := sorry

/-- The universal map out of a biproduct is computed by adding its components. -/
@[simp, stacks 09JJ "coordinate formula for a biproduct descent"]
theorem desc_hom {M N P : DifferentialGradedModule.{u, v} A}
    (f : M ⟶ P) (g : N ⟶ P) (n : ℤ) :
    (desc f g).hom n = (f.hom n).coprod (g.hom n) := sorry

/-- A map of explicit biproducts is computed componentwise. -/
@[simp, stacks 09JJ "coordinate formula for a map of DG-module biproducts"]
theorem map_hom {M N M' N' : DifferentialGradedModule.{u, v} A}
    (f : M ⟶ M') (g : N ⟶ N') (n : ℤ) :
    (map f g).hom n = (f.hom n).prodMap (g.hom n) := sorry

/-- The four coordinate maps form a binary bicone on the explicit biproduct. -/
@[stacks 09JJ "binary bicone for the explicit DG-module biproduct"]
def bicone (M N : DifferentialGradedModule.{u, v} A) : BinaryBicone M N where
  pt := biproduct M N
  fst := fst M N
  snd := snd M N
  inl := inl M N
  inr := inr M N
  inl_fst := sorry
  inl_snd := sorry
  inr_fst := sorry
  inr_snd := sorry

/-- The coordinate idempotents of the explicit biproduct sum to the identity. -/
@[stacks 09JJ "total relation for the explicit DG-module biproduct"]
theorem total (M N : DifferentialGradedModule.{u, v} A) :
    (bicone M N).fst ≫ (bicone M N).inl +
        (bicone M N).snd ≫ (bicone M N).inr = 𝟙 (bicone M N).pt := sorry

/-- The explicit degreewise product, together with its canonical binary-biproduct structure. -/
@[stacks 09JJ "binary biproduct data for differential graded modules"]
def data (M N : DifferentialGradedModule.{u, v} A) : BinaryBiproductData M N where
  bicone := bicone M N
  isBilimit := isBinaryBilimitOfTotal (bicone M N) (total M N)

end Biprod

/-- Right differential graded modules over a fixed algebra have canonical binary biproducts. -/
@[stacks 09JJ "binary biproducts of differential graded modules"]
instance instHasBinaryBiproducts (A : CochainDGAlgebra R) :
    HasBinaryBiproducts (DifferentialGradedModule.{u, v} A) where
  has_binary_biproduct M N := HasBinaryBiproduct.mk (Biprod.data M N)

namespace Biprod

/-- The categorical binary biproduct is canonically isomorphic to the explicit degreewise model. -/
@[stacks 09JJ "categorical and explicit DG-module biproduct comparison"]
noncomputable def iso (M N : DifferentialGradedModule.{u, v} A) :
    M ⊞ N ≅ biproduct M N :=
  IsLimit.conePointUniqueUpToIso
    (BinaryBiproduct.isLimit M N) (data M N).isBilimit.isLimit

/-- The comparison from the categorical biproduct preserves the first projection. -/
@[simp, stacks 09JJ "first projection of the DG-module biproduct comparison"]
theorem iso_hom_fst (M N : DifferentialGradedModule.{u, v} A) :
    (iso M N).hom ≫ fst M N = biprod.fst := sorry

/-- The comparison from the categorical biproduct preserves the second projection. -/
@[simp, stacks 09JJ "second projection of the DG-module biproduct comparison"]
theorem iso_hom_snd (M N : DifferentialGradedModule.{u, v} A) :
    (iso M N).hom ≫ snd M N = biprod.snd := sorry

/-- The comparison from the categorical biproduct preserves the first inclusion. -/
@[simp, stacks 09JJ "first inclusion of the DG-module biproduct comparison"]
theorem inl_iso_hom (M N : DifferentialGradedModule.{u, v} A) :
    biprod.inl ≫ (iso M N).hom = inl M N := sorry

/-- The comparison from the categorical biproduct preserves the second inclusion. -/
@[simp, stacks 09JJ "second inclusion of the DG-module biproduct comparison"]
theorem inr_iso_hom (M N : DifferentialGradedModule.{u, v} A) :
    biprod.inr ≫ (iso M N).hom = inr M N := sorry

/-- The inverse biproduct comparison preserves the first projection. -/
@[simp, stacks 09JJ "inverse first projection of the DG-module biproduct comparison"]
theorem iso_inv_fst (M N : DifferentialGradedModule.{u, v} A) :
    (iso M N).inv ≫ biprod.fst = fst M N := sorry

/-- The inverse biproduct comparison preserves the second projection. -/
@[simp, stacks 09JJ "inverse second projection of the DG-module biproduct comparison"]
theorem iso_inv_snd (M N : DifferentialGradedModule.{u, v} A) :
    (iso M N).inv ≫ biprod.snd = snd M N := sorry

/-- The inverse biproduct comparison preserves the first inclusion. -/
@[simp, stacks 09JJ "inverse first inclusion of the DG-module biproduct comparison"]
theorem inl_iso_inv (M N : DifferentialGradedModule.{u, v} A) :
    inl M N ≫ (iso M N).inv = biprod.inl := sorry

/-- The inverse biproduct comparison preserves the second inclusion. -/
@[simp, stacks 09JJ "inverse second inclusion of the DG-module biproduct comparison"]
theorem inr_iso_inv (M N : DifferentialGradedModule.{u, v} A) :
    inr M N ≫ (iso M N).inv = biprod.inr := sorry

end Biprod

end DifferentialGradedModule
