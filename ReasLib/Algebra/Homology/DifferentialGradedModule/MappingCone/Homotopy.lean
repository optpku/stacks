/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy
public import ReasLib.Algebra.Homology.DifferentialGradedModule.MappingCone

/-!
# Homotopy Functoriality of Differential Graded Mapping Cones

A square of right differential graded module maps that commutes up to a specified homotopy induces
an explicit upper-triangular map of mapping cones.  The strict-square map is recovered by using the
zero homotopy attached to an equality.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedModule.MappingCone

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra R}
variable {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, v} A}
variable {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂}
variable {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂}

/-- The degree-`n + 1` component of a degree-`-1` homotopy, transported to degree `n`. -/
def homotopyComponent (H : Homotopy (f₁ ≫ b) (a ≫ f₂)) (n : ℤ) :
    K₁.X (n + 1) →ₗ[R] L₂.X n :=
  ModuleCat.castLinearMap (congrArg L₂.X (Int.add_neg_cancel_right n 1)) (H.hom (n + 1))

/-- Applying the transported homotopy component is transport of the original degree-`-1` map. -/
@[simp] theorem homotopyComponent_apply (H : Homotopy (f₁ ≫ b) (a ≫ f₂))
    (n : ℤ) (x : K₁.X (n + 1)) :
    homotopyComponent H n x =
      cast (congrArg (fun X : ModuleCat.{v} R ↦ (X : Type v))
        (congrArg L₂.X (Int.add_neg_cancel_right n 1))) (H.hom (n + 1) x) := sorry

/-- The upper-triangular mapping-cone map induced by a homotopy-commutative square.  In degree
`n`, relative to the order `Lⁿ × Kⁿ⁺¹`, its matrix is `(b, H; 0, a)`. -/
def mapOfHomotopy (H : Homotopy (f₁ ≫ b) (a ≫ f₂)) :
    mappingCone f₁ ⟶ mappingCone f₂ where
  hom n :=
    ((b.hom n).coprod (homotopyComponent H n)).prod
      ((0 : L₁.X n →ₗ[R] K₂.X (n + 1)).coprod (a.hom (n + 1)))
  comm_d := sorry
  comm_smul := sorry

/-- The degreewise map induced by a homotopy-commutative square is the expected upper-triangular
matrix. -/
@[simp] theorem mapOfHomotopy_hom (H : Homotopy (f₁ ≫ b) (a ≫ f₂)) (n : ℤ) :
    (mapOfHomotopy H).hom n =
      ((b.hom n).coprod (homotopyComponent H n)).prod
        ((0 : L₁.X n →ₗ[R] K₂.X (n + 1)).coprod (a.hom (n + 1))) := sorry

/-- The cone map associated to a strictly commutative square is the homotopy cone map for its
zero homotopy. -/
theorem map_eq_mapOfHomotopy (comm : f₁ ≫ b = a ≫ f₂) :
    map a b comm = mapOfHomotopy (Homotopy.ofEq comm) := sorry

/-- A homotopy cone map preserves the canonical inclusion of the target. -/
@[reassoc] theorem inclusion_mapOfHomotopy
    (H : Homotopy (f₁ ≫ b) (a ≫ f₂)) :
    inclusion f₁ ≫ mapOfHomotopy H = b ≫ inclusion f₂ := sorry

/-- A homotopy cone map preserves the projection to the shifted source. -/
@[reassoc] theorem mapOfHomotopy_projection
    (H : Homotopy (f₁ ≫ b) (a ≫ f₂)) :
    mapOfHomotopy H ≫ projection f₂ =
      projection f₁ ≫ (shiftMap a 1 : shift K₁ 1 ⟶ shift K₂ 1) := sorry

/-- The top square of a homotopy-commutative square becomes strictly commutative in the DG
homotopy category. -/
theorem toK_square (H : Homotopy (f₁ ≫ b) (a ≫ f₂)) :
    (toK A).map f₁ ≫ (toK A).map b =
      (toK A).map a ≫ (toK A).map f₂ := sorry

/-- The target-inclusion square induced by `mapOfHomotopy` remains commutative after passage to
the DG homotopy category. -/
theorem toK_inclusion_mapOfHomotopy
    (H : Homotopy (f₁ ≫ b) (a ≫ f₂)) :
    (toK A).map (inclusion f₁) ≫ (toK A).map (mapOfHomotopy H) =
      (toK A).map b ≫ (toK A).map (inclusion f₂) := sorry

/-- The shifted-source projection square induced by `mapOfHomotopy` remains commutative after
passage to the DG homotopy category. -/
theorem toK_mapOfHomotopy_projection
    (H : Homotopy (f₁ ≫ b) (a ≫ f₂)) :
    (toK A).map (mapOfHomotopy H) ≫ (toK A).map (projection f₂) =
      (toK A).map (projection f₁) ≫ (toK A).map (shiftMap a 1) := sorry

end DifferentialGradedModule.MappingCone
