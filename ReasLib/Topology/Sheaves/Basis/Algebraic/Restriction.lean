module

public import Mathlib.Topology.Sheaves.Functors
public import ReasLib.Topology.Sheaves.Basis.Algebraic.Comparison
public import Mathlib.CategoryTheory.Whiskering

/-!
# Restriction of algebraic sheaves to a topological basis

The explicit restriction functor is definitionally sectionwise restriction, complementing the
abstract inverse of the dense-subsite comparison equivalence.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace

universe u v w u1

variable {X : TopCat.{u}}
variable {C : Type v} [Category.{w} C]
variable {F : C ⥤ Type u1} [IsAlgebraicStructure C F]
variable {B : Set (Opens X)}
variable [HasLimitsOfSize.{u, u} C] [PreservesLimitsOfSize.{u, u} F]

namespace AlgebraicBasisSheaf

/-- Restricting a `C`-valued sheaf to the members of a topological basis gives an
`AlgebraicBasisSheaf F B`. -/
theorem restrictionPresheaf_isBasisSheaf (hB : Opens.IsBasis B)
    (ℱ : TopCat.Sheaf C X) :
    Presheaf.IsBasisSheaf (((basisOpenInclusion B).op ⋙ ℱ.presheaf) ⋙ F) := sorry

/-- The inverse algebraic basis comparison has underlying presheaf given by literal restriction
along the inclusion of basis opens. -/
theorem comparisonInverse_obj (hB : Opens.IsBasis B)
    (ℱ : TopCat.Sheaf C X) :
    ((algebraicBasisSheafComparisonEquiv (F := F) hB).inverse.obj ℱ).obj =
      (basisOpenInclusion B).op ⋙ ℱ.presheaf := sorry

/-- Restriction of `C`-valued sheaves on `X` to algebraic-structure-valued sheaves on the
topological basis `B`. -/
def restriction (hB : Opens.IsBasis B) :
    TopCat.Sheaf C X ⥤ AlgebraicBasisSheaf F B where
  obj ℱ :=
    ⟨(basisOpenInclusion B).op ⋙ ℱ.presheaf,
      restrictionPresheaf_isBasisSheaf hB ℱ⟩
  map f := ObjectProperty.homMk
    (Functor.whiskerLeft (basisOpenInclusion B).op f.hom)

/-- Restriction from `C`-valued sheaves on a space to algebraic-structure-valued sheaves on a
topological basis is an equivalence. -/
instance restriction_isEquivalence (hB : Opens.IsBasis B) :
    (restriction (F := F) hB).IsEquivalence := sorry

section

variable {D : Type v} [Category.{u} D]
variable {G : D ⥤ Type u1} [IsAlgebraicStructure D G]
variable [HasLimitsOfSize.{w, w} D] [PreservesLimitsOfSize.{w, w} G]
variable {Y Z : TopCat.{w}} (f : Y ⟶ Z)
variable {ℱ : Y.Sheaf D} {𝒢 : Z.Sheaf D}
variable {BZ : Set (Opens Z)} (hBZ : Opens.IsBasis BZ)

/-- A morphism between restrictions to a topological basis extends uniquely to a morphism from
the source sheaf to the relevant pushforward. -/
theorem existsUnique_pushforwardHom_of_restriction
    (φB : (restriction (F := G) hBZ).obj 𝒢 ⟶
      (restriction (F := G) hBZ).obj ((TopCat.Sheaf.pushforward D f).obj ℱ)) :
    ∃! φ : 𝒢 ⟶ (TopCat.Sheaf.pushforward D f).obj ℱ,
      (restriction (F := G) hBZ).map φ = φB := sorry

end

end AlgebraicBasisSheaf
