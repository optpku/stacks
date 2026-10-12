/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import stacks_project.Chap85.Lemma_85_33_1_Etale
public import stacks_project.Chap85.Lemma_85_33_2_Cartesian
public import stacks_project.Chap85.Lemma_85_33_2_Equivalence

/-!
# Derived adjunction of the spaces-étale augmentation

The Section 85.32 morphism of topoi `a : Sh(U_étale) ⟶ Sh(X_étale)` has exact inverse
image `a⁻¹` on abelian sheaves. This leaf names the bounded-below derived functors
`a⁻¹` and `Ra_*`, the derived adjunction, and the canonical unit `K ⟶ Ra_* a⁻¹ K`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open Functor
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}}

/-- Sheaves of abelian groups in universe `u + 1` on the spaces-étale site admit
sheafification. -/
instance hasSheafify_spacesEtaleTopology_addCommGrpCat (Y : AlgebraicSpace S) :
    HasSheafify (spacesEtaleTopology Y) AddCommGrpCat.{u + 1} :=
  sorry

variable {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Inverse image `a⁻¹` of abelian sheaves preserves finite limits. -/
instance inverseImage_preservesFiniteLimits_addCommGrp :
    PreservesFiniteLimits (inverseImage U AddCommGrpCat.{u + 1} a) :=
  sorry

/-- Inverse image `a⁻¹` of abelian sheaves preserves finite colimits. -/
instance inverseImage_preservesFiniteColimits_addCommGrp :
    PreservesFiniteColimits (inverseImage U AddCommGrpCat.{u + 1} a) :=
  sorry

/-- The exact inverse-image functor `a⁻¹` on abelian sheaves along the spaces-étale
augmentation. -/
def inverseImageExact :
    Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1} ⥤ₑ
      Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1} :=
  ExactFunctor.of (inverseImage U AddCommGrpCat.{u + 1} a)

/-- The underlying functor of `inverseImageExact` is inverse image along the spaces-étale
augmentation. -/
theorem inverseImageExact_obj :
    (inverseImageExact a).obj = inverseImage U AddCommGrpCat.{u + 1} a :=
  sorry

/-- Direct image `a_*` of abelian sheaves along the spaces-étale augmentation is additive. -/
instance directImage_additive_addCommGrp :
    (directImage U AddCommGrpCat.{u + 1} a).Additive :=
  inferInstanceAs
    ((augmentationFunctor U a).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (spacesEtaleTopology X) (spacesEtaleTotalTopology U)).Additive

/-- The bounded-below right-derived functor of `a_*` exists. -/
instance directImage_hasRightDerivedFunctor :
    (directImage U AddCommGrpCat.{u + 1} a).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1})) :=
  sorry

/-- Bounded-below derived inverse image `a⁻¹` on `D⁺(X_étale)`. -/
def plusInverseImage :
    DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}) :=
  Adjunction.Derived.Plus.left (inverseImageExact a)

/-- Derived inverse image `a⁻¹` is the exact-left bounded-below derived functor of abelian
`a⁻¹`. -/
theorem plusInverseImage_eq :
    plusInverseImage a = Adjunction.Derived.Plus.left (inverseImageExact a) :=
  sorry

/-- Bounded-below derived direct image `Ra_*` on `D⁺(U_étale)`. -/
def plusDirectImage :
    DerivedCategory.Plus (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) :=
  Adjunction.Derived.Plus.right (directImage U AddCommGrpCat.{u + 1} a)

/-- Derived direct image `Ra_*` is the bounded-below right-derived functor of abelian `a_*`. -/
theorem plusDirectImage_eq :
    plusDirectImage a = Adjunction.Derived.Plus.right (directImage U AddCommGrpCat.{u + 1} a) :=
  sorry

/-- Bounded-below derived adjunction `a⁻¹ ⊣ Ra_*` on `D⁺`. -/
def plusAdjunction : plusInverseImage a ⊣ plusDirectImage a :=
  Adjunction.Derived.Plus.adjunction (inverseImageExact a)
    (directImage U AddCommGrpCat.{u + 1} a)
    (sheafLocalizationAdjunction a AddCommGrpCat.{u + 1})

/-- The `D⁺` adjunction `a⁻¹ ⊣ Ra_*` is the exact-left bounded-below derived adjunction of
abelian `a⁻¹ ⊣ a_*`. -/
theorem plusAdjunction_eq :
    plusAdjunction a =
      Adjunction.Derived.Plus.adjunction (inverseImageExact a)
        (directImage U AddCommGrpCat.{u + 1} a)
        (sheafLocalizationAdjunction a AddCommGrpCat.{u + 1}) :=
  sorry

/-- The canonical `D⁺` derived unit `K ⟶ Ra_* a⁻¹ K`. -/
def plusDerivedUnit :
    𝟭 (DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) ⟶
      plusInverseImage a ⋙ plusDirectImage a :=
  (plusAdjunction a).unit

/-- `plusDerivedUnit` is the unit of `plusAdjunction`. -/
theorem plusDerivedUnit_eq : plusDerivedUnit a = (plusAdjunction a).unit :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
