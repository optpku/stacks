/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Admissible.Triangle
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Admissible.Factorization
public import ReasLib.Algebra.Homology.DifferentialGradedModule.MappingCone.Admissible

/-!
# Comparing Admissible Triangles with Mapping-Cone Triangles

This file gives the intrinsic DG-module comparisons between a triangle associated to a graded
`A`-linearly split short complex and a standard mapping-cone triangle.  The comparison maps are
kept explicit; only their homotopy and triangle laws are deferred.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Pretriangulated DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedModule.ShortComplex

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra R}
variable (S : CategoryTheory.ShortComplex (DifferentialGradedModule.{u, v} A))

/-- The connecting morphism shifted down once and transported across the canonical cancellation
`(S.X₁[1])[-1] ≅ S.X₁`. -/
def deshiftConnectingHom (sigma : GradedSplitting S) : shift S.X₃ (-1) ⟶ S.X₁ :=
  shiftMap sigma.connectingHom (-1) ≫
    (Shift.addApp S.X₁ 1 (-1)).inv ≫ (Shift.zeroApp S.X₁).hom

/-- Reindexing identifies degree `n` with degree `(n + 1) - 1` in a shift down and back up. -/
theorem deshiftedThirdIndex (n : ℤ) : n = (n + 1) + (-1) := sorry

/-- The last map of the deshifted associated triangle is `S.g`, transported into
`(shift (shift S.X₃ (-1)) 1)`. -/
def deshiftedThirdHom : S.X₂ ⟶ shift (shift S.X₃ (-1)) 1 where
  hom n := ModuleCat.castLinearMap (congrArg S.X₃.X (deshiftedThirdIndex n)) (S.g.hom n)
  comm_d := sorry
  comm_smul := sorry

/-- The module-level deshifted presentation `(S.X₃[-1], S.X₁, S.X₂)` of an associated
triangle. -/
def deshiftedTriangle (sigma : GradedSplitting S) :
    Triangle (DifferentialGradedModule.{u, v} A) :=
  Triangle.mk (deshiftConnectingHom S sigma) S.f (deshiftedThirdHom S)

/-- The deshifted associated triangle in the intrinsic DG homotopy category. -/
def deshiftedTriangleK (sigma : GradedSplitting S) :
    Triangle (K R (DifferentialGradedModule.{u, v} A)) :=
  (toK A).mapTriangle.obj (deshiftedTriangle S sigma)

/-- With a chosen graded splitting, the deshifted associated triangle is isomorphic to the
standard mapping-cone triangle of the deshifted connecting morphism. -/
theorem nonempty_deshiftedTriangleIso (sigma : GradedSplitting S) :
    Nonempty
      (deshiftedTriangleK S sigma ≅ MappingCone.triangleK (deshiftConnectingHom S sigma)) := sorry

/-- Lemma 22.9.2 (09KC): an admissible short exact sequence admits a graded splitting for which
the deshifted associated triangle is isomorphic to the mapping-cone triangle of the deshifted
connecting morphism. -/
@[stacks 09KC]
theorem exists_deshiftedTriangleIso_of_admissible
    (hS : DifferentialGradedModule.IsAdmissibleShortExact S) :
    ∃ sigma : GradedSplitting S,
      Nonempty
        (deshiftedTriangleK S sigma ≅
          MappingCone.triangleK (deshiftConnectingHom S sigma)) := sorry

/-- Projection from `mappingCone S.f` to the quotient term: retain the middle-term coordinate
and apply `S.g`. -/
def coneProjection : mappingCone S.f ⟶ S.X₃ where
  hom n := (S.g.hom n).comp (LinearMap.fst R (S.X₂.X n) (S.X₁.X (n + 1)))
  comm_d := sorry
  comm_smul := sorry

/-- The projection comparison is degreewise the first cone projection followed by `S.g`. -/
@[simp]
theorem coneProjection_hom (n : ℤ) :
    (coneProjection S).hom n =
      (S.g.hom n).comp (LinearMap.fst R (S.X₂.X n) (S.X₁.X (n + 1))) := sorry

/-- A chosen graded splitting gives the explicit inverse representative
`m ↦ (sigma.s m, -sigma.connectingCoordinate m)` to the cone projection. -/
def coneSection (sigma : GradedSplitting S) : S.X₃ ⟶ mappingCone S.f where
  hom n := (sigma.s.hom n).prod (-sigma.connectingCoordinate n)
  comm_d := sorry
  comm_smul := sorry

/-- The cone section has the textbook coordinates `(sigma.s, -delta)`. -/
@[simp]
theorem coneSection_hom (sigma : GradedSplitting S) (n : ℤ) :
    (coneSection S sigma).hom n =
      (sigma.s.hom n).prod (-sigma.connectingCoordinate n) := sorry

/-- The explicit cone section is a right inverse to the cone projection. -/
theorem coneSection_projection (sigma : GradedSplitting S) :
    coneSection S sigma ≫ coneProjection S = 𝟙 S.X₃ := sorry

/-- The other composite of the cone projection and section is homotopic to the identity. -/
theorem nonempty_coneProjection_section_homotopy (sigma : GradedSplitting S) :
    Nonempty
      (Homotopy (coneProjection S ≫ coneSection S sigma) (𝟙 (mappingCone S.f))) := sorry

/-- The projection `mappingCone S.f ⟶ S.X₃` and its explicit section form an isomorphism after
passage to the DG homotopy category. -/
def coneComparisonIsoK (sigma : GradedSplitting S) :
    (toK A).obj (mappingCone S.f) ≅ (toK A).obj S.X₃ where
  hom := (toK A).map (coneProjection S)
  inv := (toK A).map (coneSection S sigma)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of the cone comparison is represented by projection to `S.X₂` followed by
`S.g`. -/
@[simp]
theorem coneComparisonIsoK_hom (sigma : GradedSplitting S) :
    (coneComparisonIsoK S sigma).hom = (toK A).map (coneProjection S) := sorry

/-- The inverse map of the cone comparison is represented by `(sigma.s, -delta)`. -/
@[simp]
theorem coneComparisonIsoK_inv (sigma : GradedSplitting S) :
    (coneComparisonIsoK S sigma).inv = (toK A).map (coneSection S sigma) := sorry

/-- Lemma 22.9.4 (1) (09KF): for a chosen graded splitting, the mapping-cone triangle of
`S.f` is isomorphic to the associated triangle, by the identity on the first two vertices and
the explicit cone comparison on the third. -/
@[stacks 09KF]
def mappingConeTriangleIso (sigma : GradedSplitting S) :
    MappingCone.triangleK S.f ≅ associatedTriangleK S sigma :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (coneComparisonIsoK S sigma)
    sorry sorry sorry

/-- The admissible-sequence comparison is the identity on its first vertex. -/
@[simp]
theorem mappingConeTriangleIso_hom₁ (sigma : GradedSplitting S) :
    (mappingConeTriangleIso S sigma).hom.hom₁ = 𝟙 _ := sorry

/-- The admissible-sequence comparison is the identity on its second vertex. -/
@[simp]
theorem mappingConeTriangleIso_hom₂ (sigma : GradedSplitting S) :
    (mappingConeTriangleIso S sigma).hom.hom₂ = 𝟙 _ := sorry

/-- The third component of the admissible-sequence comparison is the explicit cone projection
isomorphism in the DG homotopy category. -/
@[simp]
theorem mappingConeTriangleIso_hom₃ (sigma : GradedSplitting S) :
    (mappingConeTriangleIso S sigma).hom.hom₃ = (coneComparisonIsoK S sigma).hom := sorry

/-- A morphism has an associated cone row when its mapping-cone triangle is associated to an
admissible short exact sequence whose first map is that morphism. -/
def HasAssociatedConeRow {K L : DifferentialGradedModule.{u, v} A} (f : K ⟶ L) : Prop :=
  ∃ (Q : DifferentialGradedModule.{u, v} A) (g : L ⟶ Q) (zero : f ≫ g = 0),
    DifferentialGradedModule.IsAdmissibleShortExact
        (CategoryTheory.ShortComplex.mk f g zero) ∧
      ∃ sigma : GradedSplitting (CategoryTheory.ShortComplex.mk f g zero),
        Nonempty
          (MappingCone.triangleK f ≅
            associatedTriangleK (CategoryTheory.ShortComplex.mk f g zero) sigma)

/-- An admissible monomorphism has an admissible quotient row whose associated triangle is its
mapping-cone triangle. -/
theorem hasAssociatedConeRow_of_admissibleMono
    {K L : DifferentialGradedModule.{u, v} A} (f : K ⟶ L)
    (hf : DifferentialGradedModule.IsAdmissibleMono f) : HasAssociatedConeRow f := sorry

end DifferentialGradedModule.ShortComplex

namespace DifferentialGradedModule.SplitMonoFactorization

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra R}
variable {K L : DifferentialGradedModule.{u, v} A}

/-- The factorization inclusion and target projection form the strict square used for the
forward map between their mapping-cone triangles. -/
theorem triangleSquare (f : K ⟶ L) :
    inclusion f ≫ projection K L = (𝟙 K) ≫ f := sorry

/-- The reverse square, using the canonical target section, commutes up to the contraction of
the identity-cone summand. -/
def reverseTriangleHomotopy (f : K ⟶ L) :
    Homotopy (f ≫ section_ K L) ((𝟙 K) ≫ inclusion f) where
  hom :=
    ((((MappingCone.homotopyToZero K).symm.compLeft (MappingCone.inclusion (𝟙 K))).compRight
      (coneInclusion K L))).hom
  condition := sorry

/-- The forward morphism from the cone triangle of the admissible replacement to the cone
triangle of the original map. -/
def triangleMapK (f : K ⟶ L) :
    MappingCone.triangleK (inclusion f) ⟶ MappingCone.triangleK f :=
  MappingCone.triangleMapK (𝟙 K) (projection K L) (triangleSquare f)

/-- The reverse morphism of cone triangles induced by the homotopy-commutative square with the
canonical target section. -/
def triangleMapKInv (f : K ⟶ L) :
    MappingCone.triangleK f ⟶ MappingCone.triangleK (inclusion f) :=
  MappingCone.triangleMapKOfHomotopy (reverseTriangleHomotopy f)

/-- Lemma 22.9.4 (2) (09KF): the cone triangle of the canonical admissibly monic replacement
`inclusion f` is explicitly isomorphic to the cone triangle of `f`; the comparison is the
identity on the source and the canonical homotopy-equivalence projection on the target. -/
@[stacks 09KF]
def triangleIso (f : K ⟶ L) :
    MappingCone.triangleK (inclusion f) ≅ MappingCone.triangleK f where
  hom := triangleMapK f
  inv := triangleMapKInv f
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The factorization triangle comparison is the identity on the source vertex. -/
@[simp]
theorem triangleIso_hom₁ (f : K ⟶ L) :
    (triangleIso f).hom.hom₁ = 𝟙 _ := sorry

/-- The factorization triangle comparison is the canonical projection on the target vertex. -/
@[simp]
theorem triangleIso_hom₂ (f : K ⟶ L) :
    (triangleIso f).hom.hom₂ = (toK A).map (projection K L) := sorry

/-- The source cone triangle in `triangleIso f` is associated to an admissible short exact
sequence because `inclusion f` is admissibly monic. -/
theorem triangle_hasAssociatedConeRow (f : K ⟶ L) :
    ShortComplex.HasAssociatedConeRow (inclusion f) := sorry

end DifferentialGradedModule.SplitMonoFactorization
