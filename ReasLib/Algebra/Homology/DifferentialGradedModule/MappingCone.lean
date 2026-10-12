/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Biproduct
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Forget
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Shift

/-!
# Mapping Cones of Differential Graded Modules

This leaf owns the mapping cone of a morphism of right differential graded modules.  The
construction uses the textbook ordering `L^n × K^(n + 1)`, exposes its two standard maps and
strict functoriality, and compares the underlying complex with Mathlib's canonical mapping cone.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra R}

/-- Reassociates the target degree of the second summand in the mapping-cone action. -/
theorem mappingCone_smul_index (p i : ℤ) :
    (p + 1) + i = (p + i) + 1 := sorry

/-- The degree-`n` term of the mapping cone of `f : K ⟶ L`. -/
def mappingConeTerm {K L : DifferentialGradedModule.{u, v} A} (n : ℤ) :
    ModuleCat.{v} R :=
  ModuleCat.of R (L.X n × K.X (n + 1))

/-- The matrix differential `(d_L, f; 0, -d_K)` on a mapping cone. -/
def mappingConeDifferential {K L : DifferentialGradedModule.{u, v} A}
    (f : K ⟶ L) (n : ℤ) : mappingConeTerm (K := K) (L := L) n →ₗ[R]
      mappingConeTerm (K := K) (L := L) (n + 1) :=
  ((L.d n).coprod (f.hom (n + 1))).prod
    ((0 : L.X n →ₗ[R] K.X ((n + 1) + 1)).coprod (-K.d (n + 1)))

/-- The diagonal right action on a mapping-cone term. -/
def mappingConeSmul {K L : DifferentialGradedModule.{u, v} A} (p i : ℤ) :
    mappingConeTerm (K := K) (L := L) p →ₗ[R] A.X i →ₗ[R]
      mappingConeTerm (K := K) (L := L) (p + i) where
  toFun x :=
    (L.smul p i x.1).prod
      (ModuleCat.castLinearMap (congrArg K.X (mappingCone_smul_index p i))
        (K.smul (p + 1) i x.2))
  map_add' := sorry
  map_smul' := sorry

/-- Definition 22.6.1: the mapping cone of a morphism of right differential graded modules,
with degree-`n` term `L^n × K^(n + 1)` and differential `(d_L, f; 0, -d_K)`. -/
@[stacks 09KA]
def mappingCone {K L : DifferentialGradedModule.{u, v} A} (f : K ⟶ L) :
    DifferentialGradedModule A where
  X := mappingConeTerm (K := K) (L := L)
  d := mappingConeDifferential f
  smul := mappingConeSmul (K := K) (L := L)
  d_sq := sorry
  smul_one := sorry
  smul_mul := sorry
  comm_d := sorry

/-- The degree-`n` term of a mapping cone is `L^n × K^(n + 1)`. -/
@[simp] theorem mappingCone_X {K L : DifferentialGradedModule.{u, v} A}
    (f : K ⟶ L) (n : ℤ) :
    (mappingCone f).X n = ModuleCat.of R (L.X n × K.X (n + 1)) := sorry

/-- The mapping-cone differential is the textbook upper triangular matrix. -/
@[simp] theorem mappingCone_d {K L : DifferentialGradedModule.{u, v} A}
    (f : K ⟶ L) (n : ℤ) :
    (mappingCone f).d n = mappingConeDifferential f n := sorry

/-- The mapping-cone right action is diagonal on its two summands. -/
@[simp] theorem mappingCone_smul {K L : DifferentialGradedModule.{u, v} A}
    (f : K ⟶ L) (p i : ℤ) :
    (mappingCone f).smul p i = mappingConeSmul (K := K) (L := L) p i := sorry

namespace MappingCone

/-- The canonical inclusion of the target into a mapping cone. -/
def inclusion {K L : DifferentialGradedModule.{u, v} A} (f : K ⟶ L) :
    L ⟶ mappingCone f where
  hom n := LinearMap.inl R (L.X n) (K.X (n + 1))
  comm_d := sorry
  comm_smul := sorry

/-- The canonical projection from a mapping cone to the shifted source. -/
def projection {K L : DifferentialGradedModule.{u, v} A} (f : K ⟶ L) :
    mappingCone f ⟶ (shift K 1 : DifferentialGradedModule.{u, v} A) where
  hom n := LinearMap.snd R (L.X n) (K.X (n + 1))
  comm_d := sorry
  comm_smul := sorry

/-- The inclusion into a mapping cone is the first coordinate inclusion in every degree. -/
@[simp] theorem inclusion_hom {K L : DifferentialGradedModule.{u, v} A}
    (f : K ⟶ L) (n : ℤ) :
    (inclusion f).hom n = LinearMap.inl R (L.X n) (K.X (n + 1)) := sorry

/-- The projection from a mapping cone is the second coordinate projection in every degree. -/
@[simp] theorem projection_hom {K L : DifferentialGradedModule.{u, v} A}
    (f : K ⟶ L) (n : ℤ) :
    (projection f).hom n = LinearMap.snd R (L.X n) (K.X (n + 1)) := sorry

/-- A strictly commutative square induces the componentwise map between mapping cones. -/
def map {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, v} A}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂} (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : f₁ ≫ b = a ≫ f₂) : mappingCone f₁ ⟶ mappingCone f₂ where
  hom n := (b.hom n).prodMap (a.hom (n + 1))
  comm_d := sorry
  comm_smul := sorry

/-- The map of mapping cones induced by a strict square is componentwise. -/
@[simp] theorem map_hom {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, v} A}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂} (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : f₁ ≫ b = a ≫ f₂) (n : ℤ) :
    (map a b comm).hom n = (b.hom n).prodMap (a.hom (n + 1)) := sorry

/-- A strict-square cone map commutes with the canonical target inclusions. -/
theorem inclusion_naturality {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, v} A}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂} (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : f₁ ≫ b = a ≫ f₂) :
    inclusion f₁ ≫ map a b comm = b ≫ inclusion f₂ := sorry

/-- A strict-square cone map commutes with the canonical shifted-source projections. -/
theorem projection_naturality {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, v} A}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂} (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : f₁ ≫ b = a ≫ f₂) :
    map a b comm ≫ projection f₂ =
      projection f₁ ≫ (shiftMap a 1 : shift K₁ 1 ⟶ shift K₂ 1) := sorry

end MappingCone

/-- The textbook product order `L^n × K^(n + 1)` is canonically isomorphic to the degree-`n`
term of Mathlib's mapping cone of the underlying cochain map. -/
noncomputable def mappingConeXIsoCochainMappingCone
    {K L : DifferentialGradedModule.{u, v} A} (f : K ⟶ L) (n : ℤ) :
    (mappingCone f).toCochainComplex.X n ≅
      (CochainComplex.mappingCone (Hom.toCochainMap f)).X n :=
  (LinearEquiv.prodComm R (L.X n) (K.X (n + 1))).toModuleIso ≪≫
    (ModuleCat.biprodIsoProd (K.X (n + 1)) (L.X n)).symm ≪≫
      (homotopyCofiber.XIsoBiprod (Hom.toCochainMap f) n (n + 1) rfl).symm

/-- The degreewise comparison with Mathlib's mapping cone commutes with differentials. -/
theorem mappingConeXIsoCochainMappingCone_comm
    {K L : DifferentialGradedModule.{u, v} A} (f : K ⟶ L) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    (mappingConeXIsoCochainMappingCone f i).hom ≫
        (CochainComplex.mappingCone (Hom.toCochainMap f)).d i j =
      (mappingCone f).toCochainComplex.d i j ≫
        (mappingConeXIsoCochainMappingCone f j).hom := sorry

/-- The underlying cochain complex of a differential graded mapping cone is canonically
isomorphic to Mathlib's mapping cone of the underlying cochain map. -/
noncomputable def mappingConeToCochainMappingCone
    {K L : DifferentialGradedModule.{u, v} A} (f : K ⟶ L) :
    (mappingCone f).toCochainComplex ≅
      CochainComplex.mappingCone (Hom.toCochainMap f) :=
  HomologicalComplex.Hom.isoOfComponents
    (mappingConeXIsoCochainMappingCone f)
    (mappingConeXIsoCochainMappingCone_comm f)

/-- Under the canonical comparison, the DG-module cone inclusion is Mathlib's mapping-cone
inclusion of the target complex. -/
theorem mappingCone_inclusion_toCochain
    {K L : DifferentialGradedModule.{u, v} A} (f : K ⟶ L) :
    Hom.toCochainMap (MappingCone.inclusion f) ≫
        (mappingConeToCochainMappingCone f).hom =
      CochainComplex.mappingCone.inr (Hom.toCochainMap f) := sorry

end DifferentialGradedModule
