/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Admissible
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy.Property
public import ReasLib.Algebra.Homology.DifferentialGradedModule.MappingCone.Contractible

/-!
# Admissibly Monic Factorizations of Differential Graded Module Maps

A map `alpha : K ⟶ L` factors through the explicit DG-module
`L ⊞ mappingCone (𝟙 K)`.  The first map has a concrete graded `A`-linear retraction, while the
projection back to `L` has a concrete section and deformation homotopy.  Functorial maps of the
middle objects are included because finite replacement arguments consume this construction
inductively.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace DifferentialGradedModule
namespace SplitMonoFactorization

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable {K L : DifferentialGradedModule.{u, w} A}

/-- The explicit middle DG-module `L ⊞ mappingCone (𝟙 K)` in the canonical factorization. -/
@[stacks 09JW "admissibly monic factorization object"]
abbrev obj (K L : DifferentialGradedModule.{u, w} A) :
    DifferentialGradedModule.{u, w} A :=
  biproduct L (mappingCone (𝟙 K))

/-- The canonical map from the source into the factorization object. -/
@[stacks 09JW "admissibly monic factorization inclusion"]
abbrev inclusion (alpha : K ⟶ L) : K ⟶ obj K L :=
  Biprod.lift alpha (MappingCone.inclusion (𝟙 K))

/-- Projection from the factorization object to the original target. -/
@[stacks 09JW "admissibly monic factorization projection"]
abbrev projection (K L : DifferentialGradedModule.{u, w} A) : obj K L ⟶ L :=
  Biprod.fst L (mappingCone (𝟙 K))

/-- The canonical section of the target projection. -/
@[stacks 09JW "admissibly monic factorization section"]
abbrev section_ (K L : DifferentialGradedModule.{u, w} A) : L ⟶ obj K L :=
  Biprod.inl L (mappingCone (𝟙 K))

/-- Projection from the factorization object to its contractible identity-cone summand. -/
abbrev coneProjection (K L : DifferentialGradedModule.{u, w} A) :
    obj K L ⟶ mappingCone (𝟙 K) :=
  Biprod.snd L (mappingCone (𝟙 K))

/-- Inclusion of the contractible identity-cone summand into the factorization object. -/
abbrev coneInclusion (K L : DifferentialGradedModule.{u, w} A) :
    mappingCone (𝟙 K) ⟶ obj K L :=
  Biprod.inr L (mappingCone (𝟙 K))

/-- The identity maps define the commuting square used to map identity cones. -/
theorem identitySquare {K₁ K₂ : DifferentialGradedModule.{u, w} A} (a : K₁ ⟶ K₂) :
    𝟙 K₁ ≫ a = a ≫ 𝟙 K₂ := by simp

/-- Maps of sources and targets induce a componentwise map of factorization objects. -/
def map {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, w} A}
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) : obj K₁ L₁ ⟶ obj K₂ L₂ :=
  Biprod.map b (MappingCone.map a a (identitySquare a))

private theorem biprod_inl_map
    {M N M' N' : DifferentialGradedModule.{u, w} A}
    (f : M ⟶ M') (g : N ⟶ N') :
    Biprod.inl M N ≫ Biprod.map f g = f ≫ Biprod.inl M' N' := by
  apply DifferentialGradedModule.hom_ext
  intro n x
  change (Biprod.map f g).hom n ((Biprod.inl M N).hom n x) =
    (Biprod.inl M' N').hom n (f.hom n x)
  exact Prod.ext rfl (map_zero (g.hom n))

/-- The factorization inclusion is natural on strictly commuting squares. -/
theorem inclusion_naturality
    {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, w} A}
    {alpha₁ : K₁ ⟶ L₁} {alpha₂ : K₂ ⟶ L₂}
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : alpha₁ ≫ b = a ≫ alpha₂) :
    inclusion alpha₁ ≫ map a b = a ≫ inclusion alpha₂ := by
  apply DifferentialGradedModule.hom_ext
  intro n x
  exact Prod.ext (congrArg (fun f : K₁ ⟶ L₂ ↦ f.hom n x) comm)
    (Prod.ext rfl (map_zero (a.hom (n + 1))))

/-- The target projection is natural with respect to maps of factorization objects. -/
theorem map_comp_projection
    {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, w} A}
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) :
    map a b ≫ projection K₂ L₂ = projection K₁ L₁ ≫ b := by
  apply DifferentialGradedModule.hom_ext
  intro n x
  rfl

/-- The target section is natural with respect to maps of factorization objects. -/
theorem section_comp_map
    {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, w} A}
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) :
    section_ K₁ L₁ ≫ map a b = b ≫ section_ K₂ L₂ := by
  simpa [section_, map] using
    (biprod_inl_map b (MappingCone.map a a (identitySquare a)))

/-- The graded `A`-linear first-coordinate retraction of the inclusion into an identity cone. -/
def coneRetraction (K : DifferentialGradedModule.{u, w} A) :
    Graded.Hom (mappingCone (𝟙 K)).toGraded K.toGraded where
  hom n := LinearMap.fst R (K.X n) (K.X (n + 1))
  comm_smul := by
    intro p i x a
    rfl

/-- The explicit graded `A`-linear retraction of the factorization inclusion. -/
def retraction (K L : DifferentialGradedModule.{u, w} A) :
    Graded.Hom (obj K L).toGraded K.toGraded :=
  (forgetToGraded A).map (coneProjection K L) ≫ coneRetraction K

/-- The factorization inclusion followed by its graded retraction is the identity. -/
theorem inclusion_comp_retraction (alpha : K ⟶ L) :
    (forgetToGraded A).map (inclusion alpha) ≫ retraction K L = 𝟙 K.toGraded := by
  apply Graded.hom_ext
  intro n
  apply LinearMap.ext
  intro x
  rfl

/-- Lemma 22.7.4 (1) (09JW): the two displayed maps form a factorization of the original
DG-module morphism. -/
@[stacks 09JW]
theorem inclusion_comp_projection (alpha : K ⟶ L) :
    inclusion alpha ≫ projection K L = alpha := by
  apply DifferentialGradedModule.hom_ext
  intro n x
  rfl

/-- Lemma 22.7.4 (2) (09JW): the first map in the canonical factorization is an admissible
monomorphism, with graded `A`-linear retraction `retraction K L`. -/
@[stacks 09JW]
theorem isAdmissibleMono_inclusion (alpha : K ⟶ L) :
    IsAdmissibleMono (inclusion alpha) := by
  rw [isAdmissibleMono_iff_exists_retraction]
  exact ⟨retraction K L, inclusion_comp_retraction alpha⟩

/-- Lemma 22.7.4 (3) (09JW): the canonical target section is a section of the projection. -/
@[stacks 09JW]
theorem section_comp_projection (K L : DifferentialGradedModule.{u, w} A) :
    section_ K L ≫ projection K L = 𝟙 L := by
  apply DifferentialGradedModule.hom_ext
  intro n x
  rfl

/-- Adding the zero endomorphism of the identity-cone summand does not change the
projection-section composite. -/
theorem projectionSectionZero (K L : DifferentialGradedModule.{u, w} A) :
    projection K L ≫ section_ K L +
        coneProjection K L ≫ ((0 : mappingCone (𝟙 K) ⟶ mappingCone (𝟙 K)) ≫
          coneInclusion K L) =
      projection K L ≫ section_ K L := by simp

/-- The target and identity-cone coordinate idempotents add to the identity. -/
theorem projectionSectionTotal (K L : DifferentialGradedModule.{u, w} A) :
    projection K L ≫ section_ K L +
        coneProjection K L ≫ ((𝟙 (mappingCone (𝟙 K))) ≫ coneInclusion K L) =
      𝟙 (obj K L) := by
  apply DifferentialGradedModule.hom_ext
  intro n x
  exact Prod.ext (add_zero x.1) (zero_add x.2)

/-- The identity-cone contraction, included into the factorization object on both sides. -/
def coneSummandHomotopy (K L : DifferentialGradedModule.{u, w} A) :
    Homotopy
      (coneProjection K L ≫ ((0 : mappingCone (𝟙 K) ⟶ mappingCone (𝟙 K)) ≫
        coneInclusion K L))
      (coneProjection K L ≫ ((𝟙 (mappingCone (𝟙 K))) ≫ coneInclusion K L)) :=
  ((MappingCone.homotopyToZero K).symm.compRight (coneInclusion K L)).compLeft
    (coneProjection K L)

/-- Lemma 22.7.4 (4) (09JW): the projection-section composite is concretely homotopic to the
identity of the factorization object. -/
@[stacks 09JW]
def projectionHomotopy (K L : DifferentialGradedModule.{u, w} A) :
    Homotopy (projection K L ≫ section_ K L) (𝟙 (obj K L)) :=
  (Homotopy.ofEq (projectionSectionZero K L).symm).trans
    ((Homotopy.refl (projection K L ≫ section_ K L)).add (coneSummandHomotopy K L) |>.trans
      (Homotopy.ofEq (projectionSectionTotal K L)))

/-- The section-projection identity gives the reverse concrete homotopy. -/
def sectionHomotopy (K L : DifferentialGradedModule.{u, w} A) :
    Homotopy (section_ K L ≫ projection K L) (𝟙 L) :=
  Homotopy.ofEq (section_comp_projection K L)

/-- The target projection in the canonical factorization is a homotopy equivalence. -/
theorem homotopyEquivalences_projection (K L : DifferentialGradedModule.{u, w} A) :
    homotopyEquivalences A (projection K L) := by
  apply homotopyEquivalences_of_exists_inverse
  exact ⟨section_ K L, ⟨projectionHomotopy K L⟩, ⟨sectionHomotopy K L⟩⟩

end SplitMonoFactorization
end DifferentialGradedModule
