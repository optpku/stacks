module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import ReasLib.CategoryTheory.Sites.Derived.InverseImage
public import stacks_project.Chap85.Lemma_85_17_1_Equivalence

/-!
# Derived adjunction of a hypercovering

If `K` is a hypercovering of the terminal presheaf, the geometric morphism
`a : Sh((C / K)_total) → Sh(C)` presented by `j_total` has exact inverse image
`a⁻¹` and an additive direct image `a_*`. This leaf names the unbounded derived
functors `a⁻¹` and `Ra_*`, their derived adjunction, and the canonical unit
`E ⟶ Ra_* a⁻¹ E`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [h_eq : HasEqualizers C] [h_pb : HasPullbacks C]
include h_eq h_pb
variable (K : HypercoveringOf.Terminal.{w} J)
variable [HasSheafify J AddCommGrpCat.{max w u v}]
variable [HasSheafify (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}]
variable [∀ P : (Grothendieck (overSiteDiagram K.simplicial))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
    (totalForget K.simplicial).op.HasPointwiseRightKanExtension P]

/-- The exact inverse-image functor `a⁻¹` on abelian sheaves along `j_total`. -/
abbrev inverseImageExact :
    Sheaf J AddCommGrpCat.{max w u v} ⥤ₑ
      Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v} :=
  siteAbelianInverseImageExact (overSiteTotalTopology J K.simplicial) J
    (totalForget K.simplicial)

/-- The underlying functor of `inverseImageExact` is inverse image along `j_total`. -/
theorem inverseImageExact_obj :
    (inverseImageExact J K).obj =
      inverseImage J K.simplicial AddCommGrpCat.{max w u v} :=
  sorry

/-- Unbounded derived inverse image `a⁻¹` on `D(C)`. -/
abbrev inverseImageDerived :
    DerivedCategory (Sheaf J AddCommGrpCat.{max w u v}) ⥤
      DerivedCategory
        (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}) :=
  Adjunction.Derived.KInjective.left (inverseImageExact J K)

/-- Unbounded derived inverse image is the exact functor `a⁻¹` on derived categories. -/
theorem inverseImageDerived_eq :
    inverseImageDerived J K = (inverseImageExact J K).mapDerivedCategory :=
  sorry

/-- Direct image `a_*` of abelian sheaves along `j_total` is additive. -/
instance directImage_additive :
    (directImage J K.simplicial AddCommGrpCat.{max w u v}).Additive :=
  (sheafLocalizationAdjunction J K AddCommGrpCat.{max w u v}).right_adjoint_additive

/-- Unbounded total right-derived direct image `Ra_*` along `j_total`. -/
abbrev directImageDerived :
    DerivedCategory
        (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}) ⥤
      DerivedCategory (Sheaf J AddCommGrpCat.{max w u v}) :=
  Adjunction.Derived.KInjective.right
    (directImage J K.simplicial AddCommGrpCat.{max w u v})

/-- Unbounded `Ra_*` is the K-injective total right-derived functor of `a_*`. -/
theorem directImageDerived_eq :
    directImageDerived J K =
      Functor.RightDerived.KInjective.functor
        (directImage J K.simplicial AddCommGrpCat.{max w u v}) :=
  sorry

/-- The unbounded derived adjunction `a⁻¹ ⊣ Ra_*` attached to a hypercovering. -/
def derivedAdjunction :
    inverseImageDerived J K ⊣ directImageDerived J K :=
  Adjunction.Derived.KInjective.adjunction (inverseImageExact J K)
    (directImage J K.simplicial AddCommGrpCat.{max w u v})
    (sheafLocalizationAdjunction J K AddCommGrpCat.{max w u v})

/-- `derivedAdjunction` is the K-injective derived adjunction of
`sheafLocalizationAdjunction`. -/
theorem derivedAdjunction_eq :
    derivedAdjunction J K =
      Adjunction.Derived.KInjective.adjunction (inverseImageExact J K)
        (directImage J K.simplicial AddCommGrpCat.{max w u v})
        (sheafLocalizationAdjunction J K AddCommGrpCat.{max w u v}) :=
  sorry

/-- The canonical derived unit `E ⟶ Ra_* a⁻¹ E`. -/
abbrev derivedUnit :
    𝟭 (DerivedCategory (Sheaf J AddCommGrpCat.{max w u v})) ⟶
      inverseImageDerived J K ⋙ directImageDerived J K :=
  (derivedAdjunction J K).unit

/-- `derivedUnit` is the unit of `derivedAdjunction`. -/
theorem derivedUnit_eq :
    derivedUnit J K = (derivedAdjunction J K).unit :=
  sorry

section Plus

variable [(directImage J K.simplicial AddCommGrpCat.{max w u v}).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}))]

/-- Bounded-below derived inverse image `a⁻¹` on `D⁺(C)`. -/
abbrev plusInverseImageDerived :
    DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w u v}) ⥤
      DerivedCategory.Plus
        (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}) :=
  Adjunction.Derived.Plus.left (inverseImageExact J K)

/-- Bounded-below derived inverse image is the exact `D⁺` action of `a⁻¹`. -/
theorem plusInverseImageDerived_eq :
    plusInverseImageDerived J K = Adjunction.Derived.Plus.left (inverseImageExact J K) :=
  sorry

/-- Bounded-below total right-derived direct image `Ra_*` on `D⁺`. -/
abbrev plusDirectImageDerived :
    DerivedCategory.Plus
        (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}) ⥤
      DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w u v}) :=
  Adjunction.Derived.Plus.right
    (directImage J K.simplicial AddCommGrpCat.{max w u v})

/-- Bounded-below `Ra_*` is the canonical `D⁺` right-derived functor of `a_*`. -/
theorem plusDirectImageDerived_eq :
    plusDirectImageDerived J K =
      Adjunction.Derived.Plus.right
        (directImage J K.simplicial AddCommGrpCat.{max w u v}) :=
  sorry

/-- The bounded-below derived adjunction `a⁻¹ ⊣ Ra_*` on `D⁺`. -/
def plusDerivedAdjunction :
    plusInverseImageDerived J K ⊣ plusDirectImageDerived J K :=
  Adjunction.Derived.Plus.adjunction (inverseImageExact J K)
    (directImage J K.simplicial AddCommGrpCat.{max w u v})
    (sheafLocalizationAdjunction J K AddCommGrpCat.{max w u v})

/-- `plusDerivedAdjunction` is the exact-left bounded-below derived adjunction of
`sheafLocalizationAdjunction`. -/
theorem plusDerivedAdjunction_eq :
    plusDerivedAdjunction J K =
      Adjunction.Derived.Plus.adjunction (inverseImageExact J K)
        (directImage J K.simplicial AddCommGrpCat.{max w u v})
        (sheafLocalizationAdjunction J K AddCommGrpCat.{max w u v}) :=
  sorry

/-- The canonical `D⁺` derived unit `E ⟶ Ra_* a⁻¹ E`. -/
abbrev plusDerivedUnit :
    𝟭 (DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w u v})) ⟶
      plusInverseImageDerived J K ⋙ plusDirectImageDerived J K :=
  (plusDerivedAdjunction J K).unit

/-- `plusDerivedUnit` is the unit of `plusDerivedAdjunction`. -/
theorem plusDerivedUnit_eq :
    plusDerivedUnit J K = (plusDerivedAdjunction J K).unit :=
  sorry

/-- On `D⁺(C)`, the derived unit `E ⟶ Ra_* a⁻¹ E` is an isomorphism. -/
theorem plusDerivedUnit_app_isIso
    (E : DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w u v})) :
    IsIso ((plusDerivedUnit J K).app E) :=
  sorry

end Plus

end CategoryTheory.SemiRepresentableFamily
