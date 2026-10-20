module

public import stacks_project.Chap104.«104_3_2_1_Sites»
public import stacks_project.Chap104.«104_3_2_1_Comparison»
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equation 104.3.2.1

The canonical comparison morphism
`L(g')_! ((f')⁻¹ G) ⟶ f⁻¹ (Lg_! G)`
of the lisse-étale (resp. flat-fppf) functoriality square associated to a
smooth (resp. flat) 1-morphism of algebraic stacks, for complexes of modules
and of abelian sheaves.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open FiberedCategoryOver.Groupoids
open RingedSite.Cocontinuous
open scoped Bicategory

noncomputable section

universe u z

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]
variable [UnivLE.{u + 1, z}]

/-- 104.3.2.1 (1) For a smooth 1-morphism `φ : X ⟶ Y` of algebraic stacks and a
complex `G` of modules on `Y` in the lisse-étale site, the canonical comparison
`L(g')_! ((f')⁻¹ G) ⟶ f⁻¹ (Lg_! G)` of the commutative square of topoi
`Sh(X_lisse,étale) ⟶ Sh(X_étale)` over `Sh(Y_lisse,étale) ⟶ Sh(Y_étale)`. -/
@[stacks 07AX]
def lisseEtaleDerivedLowerShriekComparison (φ : X ⟶ Y) [AlgebraicStack.Smooth φ]
    (G : RingedSite.Hom.ModuleDerived.{z}
      (RingedSite.ofRingSheaf (lisseEtaleTopology Y)
        (lisseEtaleInverseImageRingSheaf Y))) :
    (lisseEtaleInclusionDerivedLowerShriek X).obj
      ((lisseEtaleDerivedInverseImage φ).obj G) ⟶
      (etaleDerivedInverseImage φ).obj
        ((lisseEtaleInclusionDerivedLowerShriek Y).obj G) :=
  (lisseEtaleDerivedLowerShriekComparisonNatTrans φ).app G

/-- The lisse-étale comparison is the component of the derived lower-shriek mate
of the transported lisse-étale inverse-image square. -/
theorem lisseEtaleDerivedLowerShriekComparison_spec (φ : X ⟶ Y)
    [AlgebraicStack.Smooth φ] :
    mateEquiv
      (lisseEtaleInclusionDerivedLowerShriek.adjunction Y)
      (lisseEtaleInclusionDerivedLowerShriek.adjunction X)
      (TwoSquare.mk (lisseEtaleDerivedInverseImage φ)
        (lisseEtaleInclusionDerivedLowerShriek Y)
        (lisseEtaleInclusionDerivedLowerShriek X)
        (etaleDerivedInverseImage φ)
        (lisseEtaleDerivedLowerShriekComparisonNatTrans φ)) =
      lisseEtaleDerivedInverseImageSquare φ := sorry

/-- The lisse-étale module comparison is an isomorphism. -/
theorem lisseEtaleDerivedLowerShriekComparison.isIso (φ : X ⟶ Y)
    [AlgebraicStack.Smooth φ]
    (G : RingedSite.Hom.ModuleDerived.{z}
      (RingedSite.ofRingSheaf (lisseEtaleTopology Y)
        (lisseEtaleInverseImageRingSheaf Y))) :
    IsIso (lisseEtaleDerivedLowerShriekComparison φ G) := sorry

/-- 104.3.2.1 (2) For a flat 1-morphism `φ : X ⟶ Y` of algebraic stacks and a
complex `G` of modules on `Y` in the flat-fppf site, the canonical comparison
`L(g')_! ((f')⁻¹ G) ⟶ f⁻¹ (Lg_! G)` of the commutative square of topoi
`Sh(X_flat,fppf) ⟶ Sh(X_fppf)` over `Sh(Y_flat,fppf) ⟶ Sh(Y_fppf)`. -/
@[stacks 07AX]
def flatFppfDerivedLowerShriekComparison (φ : X ⟶ Y) [AlgebraicStack.Flat φ]
    (G : RingedSite.Hom.ModuleDerived.{z}
      (RingedSite.ofRingSheaf (flatFppfTopology Y)
        (flatFppfInverseImageRingSheaf Y))) :
    (flatFppfInclusionDerivedLowerShriek X).obj
      ((flatFppfDerivedInverseImage φ).obj G) ⟶
      (fppfDerivedInverseImage φ).obj
        ((flatFppfInclusionDerivedLowerShriek Y).obj G) :=
  (flatFppfDerivedLowerShriekComparisonNatTrans φ).app G

/-- The flat-fppf comparison is the component of the derived lower-shriek mate
of the transported flat-fppf inverse-image square. -/
theorem flatFppfDerivedLowerShriekComparison_spec (φ : X ⟶ Y)
    [AlgebraicStack.Flat φ] :
    mateEquiv
      (flatFppfInclusionDerivedLowerShriek.adjunction Y)
      (flatFppfInclusionDerivedLowerShriek.adjunction X)
      (TwoSquare.mk (flatFppfDerivedInverseImage φ)
        (flatFppfInclusionDerivedLowerShriek Y)
        (flatFppfInclusionDerivedLowerShriek X)
        (fppfDerivedInverseImage φ)
        (flatFppfDerivedLowerShriekComparisonNatTrans φ)) =
      flatFppfDerivedInverseImageSquare φ := sorry

/-- The flat-fppf module comparison is an isomorphism. -/
theorem flatFppfDerivedLowerShriekComparison.isIso (φ : X ⟶ Y)
    [AlgebraicStack.Flat φ]
    (G : RingedSite.Hom.ModuleDerived.{z}
      (RingedSite.ofRingSheaf (flatFppfTopology Y)
        (flatFppfInverseImageRingSheaf Y))) :
    IsIso (flatFppfDerivedLowerShriekComparison φ G) := sorry

/-- 104.3.2.1 (3) For a smooth 1-morphism `φ : X ⟶ Y` of algebraic stacks and a
complex `G` of abelian sheaves on `Y` in the lisse-étale site, the canonical
comparison `L(g')_! ((f')⁻¹ G) ⟶ f⁻¹ (Lg_! G)` of the commutative square of
topoi `Sh(X_lisse,étale) ⟶ Sh(X_étale)` over `Sh(Y_lisse,étale) ⟶ Sh(Y_étale)`. -/
@[stacks 07AX]
def lisseEtaleAbelianDerivedLowerShriekComparison (φ : X ⟶ Y)
    [AlgebraicStack.Smooth φ]
    (G : DerivedCategory (Sheaf (lisseEtaleTopology Y) AddCommGrpCat.{z})) :
    (lisseEtaleAbelianLowerShriekDerived X).obj
      ((lisseEtaleAbelianDerivedInverseImage φ).obj G) ⟶
      (etaleAbelianDerivedInverseImage φ).obj
        ((lisseEtaleAbelianLowerShriekDerived Y).obj G) :=
  (lisseEtaleAbelianDerivedLowerShriekComparisonNatTrans φ).app G

/-- The lisse-étale abelian comparison is the component of the derived
lower-shriek mate of the lisse-étale abelian inverse-image square. -/
theorem lisseEtaleAbelianDerivedLowerShriekComparison_spec (φ : X ⟶ Y)
    [AlgebraicStack.Smooth φ] :
    mateEquiv
      (abelianLowerShriekDerived.adjunction (lisseEtaleTopology Y) Y.etaleTopology
        (lisseEtaleInclusion Y))
      (abelianLowerShriekDerived.adjunction (lisseEtaleTopology X) X.etaleTopology
        (lisseEtaleInclusion X))
      (TwoSquare.mk (lisseEtaleAbelianDerivedInverseImage φ)
        (lisseEtaleAbelianLowerShriekDerived Y)
        (lisseEtaleAbelianLowerShriekDerived X)
        (etaleAbelianDerivedInverseImage φ)
        (lisseEtaleAbelianDerivedLowerShriekComparisonNatTrans φ)) =
      lisseEtaleAbelianDerivedInverseImageSquare φ := sorry

/-- The lisse-étale abelian comparison is an isomorphism. -/
theorem lisseEtaleAbelianDerivedLowerShriekComparison.isIso (φ : X ⟶ Y)
    [AlgebraicStack.Smooth φ]
    (G : DerivedCategory (Sheaf (lisseEtaleTopology Y) AddCommGrpCat.{z})) :
    IsIso (lisseEtaleAbelianDerivedLowerShriekComparison φ G) := sorry

/-- 104.3.2.1 (4) For a flat 1-morphism `φ : X ⟶ Y` of algebraic stacks and a
complex `G` of abelian sheaves on `Y` in the flat-fppf site, the canonical
comparison `L(g')_! ((f')⁻¹ G) ⟶ f⁻¹ (Lg_! G)` of the commutative square of
topoi `Sh(X_flat,fppf) ⟶ Sh(X_fppf)` over `Sh(Y_flat,fppf) ⟶ Sh(Y_fppf)`. -/
@[stacks 07AX]
def flatFppfAbelianDerivedLowerShriekComparison (φ : X ⟶ Y) [AlgebraicStack.Flat φ]
    (G : DerivedCategory (Sheaf (flatFppfTopology Y) AddCommGrpCat.{z})) :
    (flatFppfAbelianLowerShriekDerived X).obj
      ((flatFppfAbelianDerivedInverseImage φ).obj G) ⟶
      (fppfAbelianDerivedInverseImage φ).obj
        ((flatFppfAbelianLowerShriekDerived Y).obj G) :=
  (flatFppfAbelianDerivedLowerShriekComparisonNatTrans φ).app G

/-- The flat-fppf abelian comparison is the component of the derived
lower-shriek mate of the flat-fppf abelian inverse-image square. -/
theorem flatFppfAbelianDerivedLowerShriekComparison_spec (φ : X ⟶ Y)
    [AlgebraicStack.Flat φ] :
    mateEquiv
      (abelianLowerShriekDerived.adjunction (flatFppfTopology Y)
        (inheritedFppfTopology Y) (flatFppfInclusion Y))
      (abelianLowerShriekDerived.adjunction (flatFppfTopology X)
        (inheritedFppfTopology X) (flatFppfInclusion X))
      (TwoSquare.mk (flatFppfAbelianDerivedInverseImage φ)
        (flatFppfAbelianLowerShriekDerived Y)
        (flatFppfAbelianLowerShriekDerived X)
        (fppfAbelianDerivedInverseImage φ)
        (flatFppfAbelianDerivedLowerShriekComparisonNatTrans φ)) =
      flatFppfAbelianDerivedInverseImageSquare φ := sorry

/-- The flat-fppf abelian comparison is an isomorphism. -/
theorem flatFppfAbelianDerivedLowerShriekComparison.isIso (φ : X ⟶ Y)
    [AlgebraicStack.Flat φ]
    (G : DerivedCategory (Sheaf (flatFppfTopology Y) AddCommGrpCat.{z})) :
    IsIso (flatFppfAbelianDerivedLowerShriekComparison φ G) := sorry

end AlgebraicGeometry.AlgebraicStack
