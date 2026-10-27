/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
  map_add' := by
    intro x y
    ext a <;> simp
  map_smul' := by
    intro r x
    ext a <;> simp

/-- Transport between degrees commutes with taking the two coordinates. -/
private theorem biproduct_cast {M N : ℤ → Type v} {p q : ℤ} (h : p = q)
    (hMN : (M p × N p) = (M q × N q)) (hM : M p = M q) (hN : N p = N q)
    (x : M p × N p) : cast hMN x = (cast hM x.1, cast hN x.2) := by
  subst q
  rfl

/-- The canonical degreewise product of two right differential graded modules. -/
@[stacks 09JJ "explicit binary biproduct of differential graded modules"]
def biproduct (M N : DifferentialGradedModule.{u, v} A) :
    DifferentialGradedModule A where
  X n := ModuleCat.of R (M.X n × N.X n)
  d n := (M.d n).prodMap (N.d n)
  smul := biproductSmul M N
  d_sq := by
    intro n x
    exact Prod.ext (M.d_sq n x.1) (N.d_sq n x.2)
  smul_one := by
    intro r p x
    change (M.smul p 0 x.1 (r • A.one), N.smul p 0 x.2 (r • A.one)) = _
    rw [biproduct_cast (M := fun n ↦ M.X n) (N := fun n ↦ N.X n)
      (by omega) _ (zeroActionTarget p) (zeroActionTarget p)]
    exact Prod.ext (M.smul_one r p x.1) (N.smul_one r p x.2)
  smul_mul := by
    intro p i j x a b
    change (M.smul p (i + j) x.1 (A.mul i j a b),
      N.smul p (i + j) x.2 (A.mul i j a b)) = _
    rw [biproduct_cast (M := fun n ↦ M.X n) (N := fun n ↦ N.X n)
      (by omega) _ (mulActionTarget p i j) (mulActionTarget p i j)]
    exact Prod.ext (M.smul_mul p i j x.1 a b) (N.smul_mul p i j x.2 a b)
  comm_d := by
    intro p i x a
    change (M.d (p + i) (M.smul p i x.1 a),
      N.d (p + i) (N.smul p i x.2 a)) = _
    rw [biproduct_cast (M := fun n ↦ M.X n) (N := fun n ↦ N.X n)
      (by omega) _ (dLeftActionTarget p i) (dLeftActionTarget p i),
      biproduct_cast (M := fun n ↦ M.X n) (N := fun n ↦ N.X n)
      (by omega) _ (dRightActionTarget p i) (dRightActionTarget p i)]
    exact Prod.ext (M.comm_d p i x.1 a) (N.comm_d p i x.2 a)

/-- The degree-`n` term of the explicit biproduct is the product of the degree-`n` terms. -/
@[simp, stacks 09JJ "terms of an explicit DG-module biproduct"]
theorem biproduct_X (M N : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (biproduct M N).X n = ModuleCat.of R (M.X n × N.X n) := rfl

/-- The differential of the explicit biproduct is componentwise. -/
@[simp, stacks 09JJ "differential of an explicit DG-module biproduct"]
theorem biproduct_d (M N : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (biproduct M N).d n = (M.d n).prodMap (N.d n) := rfl

/-- The right action on the explicit biproduct is componentwise. -/
@[simp, stacks 09JJ "action on an explicit DG-module biproduct"]
theorem biproduct_smul (M N : DifferentialGradedModule.{u, v} A) (p i : ℤ) :
    (biproduct M N).smul p i = biproductSmul M N p i := rfl

namespace Biprod

/-- The first projection from the explicit biproduct of differential graded modules. -/
@[stacks 09JJ "first projection from an explicit DG-module biproduct"]
def fst (M N : DifferentialGradedModule.{u, v} A) : biproduct M N ⟶ M where
  hom n := LinearMap.fst R (M.X n) (N.X n)
  comm_d _ _ := rfl
  comm_smul _ _ _ _ := rfl

/-- The second projection from the explicit biproduct of differential graded modules. -/
@[stacks 09JJ "second projection from an explicit DG-module biproduct"]
def snd (M N : DifferentialGradedModule.{u, v} A) : biproduct M N ⟶ N where
  hom n := LinearMap.snd R (M.X n) (N.X n)
  comm_d _ _ := rfl
  comm_smul _ _ _ _ := rfl

/-- The first inclusion into the explicit biproduct of differential graded modules. -/
@[stacks 09JJ "first inclusion into an explicit DG-module biproduct"]
def inl (M N : DifferentialGradedModule.{u, v} A) : M ⟶ biproduct M N where
  hom n := LinearMap.inl R (M.X n) (N.X n)
  comm_d := by
    intro n x
    exact Prod.ext rfl (map_zero (N.d n)).symm
  comm_smul := by
    intro p i x a
    exact Prod.ext rfl
      (congrArg (fun f : A.X i →ₗ[R] N.X (p + i) ↦ f a) (map_zero (N.smul p i))).symm

/-- The second inclusion into the explicit biproduct of differential graded modules. -/
@[stacks 09JJ "second inclusion into an explicit DG-module biproduct"]
def inr (M N : DifferentialGradedModule.{u, v} A) : N ⟶ biproduct M N where
  hom n := LinearMap.inr R (M.X n) (N.X n)
  comm_d := by
    intro n x
    exact Prod.ext (map_zero (M.d n)).symm rfl
  comm_smul := by
    intro p i x a
    exact Prod.ext
      (congrArg (fun f : A.X i →ₗ[R] M.X (p + i) ↦ f a) (map_zero (M.smul p i))).symm rfl

/-- The universal map into the explicit biproduct. -/
@[stacks 09JJ "lift into an explicit DG-module biproduct"]
def lift {P M N : DifferentialGradedModule.{u, v} A} (f : P ⟶ M) (g : P ⟶ N) :
    P ⟶ biproduct M N where
  hom n := (f.hom n).prod (g.hom n)
  comm_d := by
    intro n x
    exact Prod.ext (f.comm_d n x) (g.comm_d n x)
  comm_smul := by
    intro p i x a
    exact Prod.ext (f.comm_smul p i x a) (g.comm_smul p i x a)

/-- The universal map out of the explicit biproduct. -/
@[stacks 09JJ "descent from an explicit DG-module biproduct"]
def desc {M N P : DifferentialGradedModule.{u, v} A} (f : M ⟶ P) (g : N ⟶ P) :
    biproduct M N ⟶ P where
  hom n := (f.hom n).coprod (g.hom n)
  comm_d := by
    intro n x
    change f.hom (n + 1) (M.d n x.1) + g.hom (n + 1) (N.d n x.2) =
      P.d n (f.hom n x.1 + g.hom n x.2)
    rw [map_add, f.comm_d, g.comm_d]
  comm_smul := by
    intro p i x a
    change f.hom (p + i) (M.smul p i x.1 a) + g.hom (p + i) (N.smul p i x.2 a) =
      P.smul p i (f.hom p x.1 + g.hom p x.2) a
    simp only [map_add, LinearMap.add_apply, f.comm_smul, g.comm_smul]

/-- The componentwise map between explicit biproducts. -/
@[stacks 09JJ "componentwise map of explicit DG-module biproducts"]
def map {M N M' N' : DifferentialGradedModule.{u, v} A} (f : M ⟶ M') (g : N ⟶ N') :
    biproduct M N ⟶ biproduct M' N' where
  hom n := (f.hom n).prodMap (g.hom n)
  comm_d := by
    intro n x
    exact Prod.ext (f.comm_d n x.1) (g.comm_d n x.2)
  comm_smul := by
    intro p i x a
    exact Prod.ext (f.comm_smul p i x.1 a) (g.comm_smul p i x.2 a)

/-- The first projection is the first coordinate linear map in every degree. -/
@[simp, stacks 09JJ "first projection coordinates of an explicit DG-module biproduct"]
theorem fst_hom (M N : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (fst M N).hom n = LinearMap.fst R (M.X n) (N.X n) := rfl

/-- The second projection is the second coordinate linear map in every degree. -/
@[simp, stacks 09JJ "second projection coordinates of an explicit DG-module biproduct"]
theorem snd_hom (M N : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (snd M N).hom n = LinearMap.snd R (M.X n) (N.X n) := rfl

/-- The first inclusion is the first coordinate inclusion in every degree. -/
@[simp, stacks 09JJ "first inclusion coordinates of an explicit DG-module biproduct"]
theorem inl_hom (M N : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (inl M N).hom n = LinearMap.inl R (M.X n) (N.X n) := rfl

/-- The second inclusion is the second coordinate inclusion in every degree. -/
@[simp, stacks 09JJ "second inclusion coordinates of an explicit DG-module biproduct"]
theorem inr_hom (M N : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (inr M N).hom n = LinearMap.inr R (M.X n) (N.X n) := rfl

/-- The universal map into a biproduct is computed by pairing its components. -/
@[simp, stacks 09JJ "coordinate formula for a biproduct lift"]
theorem lift_hom {P M N : DifferentialGradedModule.{u, v} A}
    (f : P ⟶ M) (g : P ⟶ N) (n : ℤ) :
    (lift f g).hom n = (f.hom n).prod (g.hom n) := rfl

/-- The universal map out of a biproduct is computed by adding its components. -/
@[simp, stacks 09JJ "coordinate formula for a biproduct descent"]
theorem desc_hom {M N P : DifferentialGradedModule.{u, v} A}
    (f : M ⟶ P) (g : N ⟶ P) (n : ℤ) :
    (desc f g).hom n = (f.hom n).coprod (g.hom n) := rfl

/-- A map of explicit biproducts is computed componentwise. -/
@[simp, stacks 09JJ "coordinate formula for a map of DG-module biproducts"]
theorem map_hom {M N M' N' : DifferentialGradedModule.{u, v} A}
    (f : M ⟶ M') (g : N ⟶ N') (n : ℤ) :
    (map f g).hom n = (f.hom n).prodMap (g.hom n) := rfl

/-- Extensionality proved directly from the components of a DG-module morphism. -/
private theorem biproduct_hom_ext {M N : DifferentialGradedModule.{u, v} A}
    {f g : M ⟶ N} (h : ∀ n x, f.hom n x = g.hom n x) : f = g := by
  have h' : f.hom = g.hom := funext fun n ↦ LinearMap.ext (h n)
  cases f
  cases g
  cases h'
  rfl

/-- The four coordinate maps form a binary bicone on the explicit biproduct. -/
@[stacks 09JJ "binary bicone for the explicit DG-module biproduct"]
def bicone (M N : DifferentialGradedModule.{u, v} A) : BinaryBicone M N where
  pt := biproduct M N
  fst := fst M N
  snd := snd M N
  inl := inl M N
  inr := inr M N
  inl_fst := by
    apply biproduct_hom_ext
    intro n x
    rfl
  inl_snd := by
    apply biproduct_hom_ext
    intro n x
    rfl
  inr_fst := by
    apply biproduct_hom_ext
    intro n x
    rfl
  inr_snd := by
    apply biproduct_hom_ext
    intro n x
    rfl

/-- The coordinate idempotents of the explicit biproduct sum to the identity. -/
@[stacks 09JJ "total relation for the explicit DG-module biproduct"]
theorem total (M N : DifferentialGradedModule.{u, v} A) :
    (bicone M N).fst ≫ (bicone M N).inl +
        (bicone M N).snd ≫ (bicone M N).inr = 𝟙 (bicone M N).pt := by
  apply biproduct_hom_ext
  intro n x
  exact Prod.ext (add_zero x.1) (zero_add x.2)

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
    (iso M N).hom ≫ fst M N = biprod.fst := by
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    (BinaryBiproduct.isLimit M N) (data M N).isBilimit.isLimit ⟨WalkingPair.left⟩

/-- The comparison from the categorical biproduct preserves the second projection. -/
@[simp, stacks 09JJ "second projection of the DG-module biproduct comparison"]
theorem iso_hom_snd (M N : DifferentialGradedModule.{u, v} A) :
    (iso M N).hom ≫ snd M N = biprod.snd := by
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    (BinaryBiproduct.isLimit M N) (data M N).isBilimit.isLimit ⟨WalkingPair.right⟩

/-- The comparison from the categorical biproduct preserves the first inclusion. -/
@[simp, stacks 09JJ "first inclusion of the DG-module biproduct comparison"]
theorem inl_iso_hom (M N : DifferentialGradedModule.{u, v} A) :
    biprod.inl ≫ (iso M N).hom = inl M N := by
  apply BinaryFan.IsLimit.hom_ext (data M N).isBilimit.isLimit
  · change (biprod.inl ≫ (iso M N).hom) ≫ fst M N = inl M N ≫ fst M N
    rw [Category.assoc, iso_hom_fst, biprod.inl_fst]
    exact (bicone M N).inl_fst.symm
  · change (biprod.inl ≫ (iso M N).hom) ≫ snd M N = inl M N ≫ snd M N
    rw [Category.assoc, iso_hom_snd, biprod.inl_snd]
    exact (bicone M N).inl_snd.symm

/-- The comparison from the categorical biproduct preserves the second inclusion. -/
@[simp, stacks 09JJ "second inclusion of the DG-module biproduct comparison"]
theorem inr_iso_hom (M N : DifferentialGradedModule.{u, v} A) :
    biprod.inr ≫ (iso M N).hom = inr M N := by
  apply BinaryFan.IsLimit.hom_ext (data M N).isBilimit.isLimit
  · change (biprod.inr ≫ (iso M N).hom) ≫ fst M N = inr M N ≫ fst M N
    rw [Category.assoc, iso_hom_fst, biprod.inr_fst]
    exact (bicone M N).inr_fst.symm
  · change (biprod.inr ≫ (iso M N).hom) ≫ snd M N = inr M N ≫ snd M N
    rw [Category.assoc, iso_hom_snd, biprod.inr_snd]
    exact (bicone M N).inr_snd.symm

/-- The inverse biproduct comparison preserves the first projection. -/
@[simp, stacks 09JJ "inverse first projection of the DG-module biproduct comparison"]
theorem iso_inv_fst (M N : DifferentialGradedModule.{u, v} A) :
    (iso M N).inv ≫ biprod.fst = fst M N := by
  exact IsLimit.conePointUniqueUpToIso_inv_comp
    (BinaryBiproduct.isLimit M N) (data M N).isBilimit.isLimit ⟨WalkingPair.left⟩

/-- The inverse biproduct comparison preserves the second projection. -/
@[simp, stacks 09JJ "inverse second projection of the DG-module biproduct comparison"]
theorem iso_inv_snd (M N : DifferentialGradedModule.{u, v} A) :
    (iso M N).inv ≫ biprod.snd = snd M N := by
  exact IsLimit.conePointUniqueUpToIso_inv_comp
    (BinaryBiproduct.isLimit M N) (data M N).isBilimit.isLimit ⟨WalkingPair.right⟩

/-- The inverse biproduct comparison preserves the first inclusion. -/
@[simp, stacks 09JJ "inverse first inclusion of the DG-module biproduct comparison"]
theorem inl_iso_inv (M N : DifferentialGradedModule.{u, v} A) :
    inl M N ≫ (iso M N).inv = biprod.inl := by
  apply (cancel_mono (iso M N).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, inl_iso_hom]

/-- The inverse biproduct comparison preserves the second inclusion. -/
@[simp, stacks 09JJ "inverse second inclusion of the DG-module biproduct comparison"]
theorem inr_iso_inv (M N : DifferentialGradedModule.{u, v} A) :
    inr M N ≫ (iso M N).inv = biprod.inr := by
  apply (cancel_mono (iso M N).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, inr_iso_hom]

end Biprod

end DifferentialGradedModule
