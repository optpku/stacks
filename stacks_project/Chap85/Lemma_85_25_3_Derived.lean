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
public import stacks_project.Chap85.Lemma_85_2_11_Pushforward
public import stacks_project.Chap85.Lemma_85_25_2_Cartesian

/-!
# Bounded-below derived adjunction of a Zariski augmentation

An augmentation `a : Y ⟶ constSpace X` of simplicial spaces has abelian inverse
image `inverseImage a AddCommGrpCat.{u}`, left adjoint to
`directImage`/`augmentationPushforward`, together with the canonical `D⁺`
adjunction and unit `K ⟶ Ra_* a⁻¹ K`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.AbelianSheaf CategoryTheory.Functor CategoryTheory.Limits TopCat

noncomputable section

universe u

namespace CategoryTheory.SimplicialObject

variable {Y : SimplicialObject TopCat.{u}} {X : TopCat.{u}} (a : Y ⟶ constSpace X)

variable [HasSheafify (zariskiTopology Y) AddCommGrpCat.{u}]
variable [HasSheafify (zariskiTopology (constSpace X)) AddCommGrpCat.{u}]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/-- The abelian inverse image `a⁻¹` of an augmentation. -/
abbrev augmentationInverseImage :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      Sheaf (zariskiTopology Y) AddCommGrpCat.{u} :=
  inverseImage a AddCommGrpCat.{u}

/-- `augmentationInverseImage a` is inverse image of abelian sheaves along `a`. -/
theorem augmentationInverseImage_eq :
    augmentationInverseImage a = inverseImage a AddCommGrpCat.{u} :=
  sorry

/-- The abelian direct image `a_*` of an augmentation agrees with `directImage`. -/
theorem augmentationPushforward_eq :
    augmentationPushforward a = directImage a AddCommGrpCat.{u} :=
  sorry

/-- Additivity of the abelian augmentation inverse image. -/
instance augmentationInverseImage_additive : (augmentationInverseImage a).Additive :=
  sorry

/-- The abelian augmentation inverse image preserves finite limits. -/
instance augmentationInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (augmentationInverseImage a) :=
  sorry

/-- The abelian augmentation inverse image preserves finite colimits. -/
instance augmentationInverseImage_preservesFiniteColimits :
    PreservesFiniteColimits (augmentationInverseImage a) :=
  sorry

/-- The exact abelian inverse-image functor `a⁻¹` of an augmentation. -/
abbrev augmentationInverseImageExact :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ₑ
      Sheaf (zariskiTopology Y) AddCommGrpCat.{u} :=
  ExactFunctor.of (augmentationInverseImage a)

/-- The underlying functor of `augmentationInverseImageExact` is `a⁻¹`. -/
theorem augmentationInverseImageExact_obj :
    (augmentationInverseImageExact a).obj = augmentationInverseImage a :=
  sorry

section Plus

variable [(augmentationPushforward a).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (zariskiTopology Y) AddCommGrpCat.{u}))]

/-- Bounded-below derived inverse image `a⁻¹` on `D⁺(X)`. -/
abbrev plusInverseImageDerived :
    DerivedCategory.Plus (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ⥤
      DerivedCategory.Plus (Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) :=
  Adjunction.Derived.Plus.left (augmentationInverseImageExact a)

/-- Bounded-below derived inverse image is the exact `D⁺` action of `a⁻¹`. -/
theorem plusInverseImageDerived_eq :
    plusInverseImageDerived a =
      Adjunction.Derived.Plus.left (augmentationInverseImageExact a) :=
  sorry

/-- Bounded-below total right-derived direct image `Ra_*` on `D⁺`. -/
abbrev plusDirectImageDerived :
    DerivedCategory.Plus (Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) ⥤
      DerivedCategory.Plus (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  Adjunction.Derived.Plus.right (augmentationPushforward a)

/-- Bounded-below `Ra_*` is the canonical `D⁺` right-derived functor of `a_*`. -/
theorem plusDirectImageDerived_eq :
    plusDirectImageDerived a =
      Adjunction.Derived.Plus.right (augmentationPushforward a) :=
  sorry

/-- The bounded-below derived adjunction `a⁻¹ ⊣ Ra_*` on `D⁺`. -/
def plusDerivedAdjunction :
    plusInverseImageDerived a ⊣ plusDirectImageDerived a :=
  Adjunction.Derived.Plus.adjunction (augmentationInverseImageExact a)
    (augmentationPushforward a) (inverseImageAdjunction a AddCommGrpCat.{u})

/-- `plusDerivedAdjunction` is the exact-left bounded-below derived adjunction of
`inverseImageAdjunction`. -/
theorem plusDerivedAdjunction_eq :
    plusDerivedAdjunction a =
      Adjunction.Derived.Plus.adjunction (augmentationInverseImageExact a)
        (augmentationPushforward a) (inverseImageAdjunction a AddCommGrpCat.{u}) :=
  sorry

/-- The canonical `D⁺` derived unit `K ⟶ Ra_* a⁻¹ K`. -/
abbrev plusDerivedUnit :
    𝟭 (DerivedCategory.Plus (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})) ⟶
      plusInverseImageDerived a ⋙ plusDirectImageDerived a :=
  (plusDerivedAdjunction a).unit

/-- `plusDerivedUnit` is the unit of `plusDerivedAdjunction`. -/
theorem plusDerivedUnit_eq :
    plusDerivedUnit a = (plusDerivedAdjunction a).unit :=
  sorry

end Plus

end CategoryTheory.SimplicialObject

end
