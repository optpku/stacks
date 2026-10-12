/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
    𝟙 K₁ ≫ a = a ≫ 𝟙 K₂ := sorry

/-- Maps of sources and targets induce a componentwise map of factorization objects. -/
def map {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, w} A}
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) : obj K₁ L₁ ⟶ obj K₂ L₂ :=
  Biprod.map b (MappingCone.map a a (identitySquare a))

/-- The factorization inclusion is natural on strictly commuting squares. -/
theorem inclusion_naturality
    {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, w} A}
    {alpha₁ : K₁ ⟶ L₁} {alpha₂ : K₂ ⟶ L₂}
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : alpha₁ ≫ b = a ≫ alpha₂) :
    inclusion alpha₁ ≫ map a b = a ≫ inclusion alpha₂ := sorry

/-- The target projection is natural with respect to maps of factorization objects. -/
theorem map_comp_projection
    {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, w} A}
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) :
    map a b ≫ projection K₂ L₂ = projection K₁ L₁ ≫ b := sorry

/-- The target section is natural with respect to maps of factorization objects. -/
theorem section_comp_map
    {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, w} A}
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) :
    section_ K₁ L₁ ≫ map a b = b ≫ section_ K₂ L₂ := sorry

/-- The graded `A`-linear first-coordinate retraction of the inclusion into an identity cone. -/
def coneRetraction (K : DifferentialGradedModule.{u, w} A) :
    Graded.Hom (mappingCone (𝟙 K)).toGraded K.toGraded where
  hom n := LinearMap.fst R (K.X n) (K.X (n + 1))
  comm_smul := sorry

/-- The explicit graded `A`-linear retraction of the factorization inclusion. -/
def retraction (K L : DifferentialGradedModule.{u, w} A) :
    Graded.Hom (obj K L).toGraded K.toGraded :=
  (forgetToGraded A).map (coneProjection K L) ≫ coneRetraction K

/-- The factorization inclusion followed by its graded retraction is the identity. -/
theorem inclusion_comp_retraction (alpha : K ⟶ L) :
    (forgetToGraded A).map (inclusion alpha) ≫ retraction K L = 𝟙 K.toGraded := sorry

/-- Lemma 22.7.4 (1) (09JW): the two displayed maps form a factorization of the original
DG-module morphism. -/
@[stacks 09JW]
theorem inclusion_comp_projection (alpha : K ⟶ L) :
    inclusion alpha ≫ projection K L = alpha := sorry

/-- Lemma 22.7.4 (2) (09JW): the first map in the canonical factorization is an admissible
monomorphism, with graded `A`-linear retraction `retraction K L`. -/
@[stacks 09JW]
theorem isAdmissibleMono_inclusion (alpha : K ⟶ L) :
    IsAdmissibleMono (inclusion alpha) := sorry

/-- Lemma 22.7.4 (3) (09JW): the canonical target section is a section of the projection. -/
@[stacks 09JW]
theorem section_comp_projection (K L : DifferentialGradedModule.{u, w} A) :
    section_ K L ≫ projection K L = 𝟙 L := sorry

/-- Adding the zero endomorphism of the identity-cone summand does not change the
projection-section composite. -/
theorem projectionSectionZero (K L : DifferentialGradedModule.{u, w} A) :
    projection K L ≫ section_ K L +
        coneProjection K L ≫ ((0 : mappingCone (𝟙 K) ⟶ mappingCone (𝟙 K)) ≫
          coneInclusion K L) =
      projection K L ≫ section_ K L := sorry

/-- The target and identity-cone coordinate idempotents add to the identity. -/
theorem projectionSectionTotal (K L : DifferentialGradedModule.{u, w} A) :
    projection K L ≫ section_ K L +
        coneProjection K L ≫ ((𝟙 (mappingCone (𝟙 K))) ≫ coneInclusion K L) =
      𝟙 (obj K L) := sorry

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
    homotopyEquivalences A (projection K L) := sorry

end SplitMonoFactorization
end DifferentialGradedModule
