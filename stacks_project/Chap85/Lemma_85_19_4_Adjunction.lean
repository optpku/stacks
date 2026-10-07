module

public import ReasLib.CategoryTheory.Limits.Over.FiniteLimits
public import stacks_project.Chap85.Lemma_85_17_3_Adjunction
public import stacks_project.Chap85.Lemma_85_19_1_Slice

/-!
# Bounded-below derived adjunction of a hypercovering of an object

If `K` is a hypercovering of an object `X`, the geometric morphism
`a : Sh((C / K)_total) → Sh(C / X)` presented by `j_total` on the slice site
`J.over X` has exact inverse image `a⁻¹` and an additive direct image `a_*`.
This leaf instantiates the bounded-below derived functors `a⁻¹` and `Ra_*`, their
derived adjunction, and the canonical unit `E ⟶ Ra_* a⁻¹ E` at
`toSliceTerminal`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SemiRepresentableFamily
  (overSiteDiagram overSiteTotalTopology totalForget directImage)
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C]
variable [h_pb : HasPullbacks C]
include h_pb
variable (J : GrothendieckTopology C) (X : C) (K : Hypercovering.{w} J X)
variable [HasSheafify (J.over X) AddCommGrpCat.{max w u v}]
variable [HasSheafify (overSiteTotalTopology (J.over X) K.toSimplicialObject)
    AddCommGrpCat.{max w u v}]
variable [∀ P : (Grothendieck (overSiteDiagram K.toSimplicialObject))ᵒᵖ ⥤
    AddCommGrpCat.{max w u v},
    (totalForget K.toSimplicialObject).op.HasPointwiseRightKanExtension P]

/-- Direct image `a_*` of abelian sheaves along `j_total` is additive for a
hypercovering of an object. -/
instance directImage_additive :
    (directImage (J.over X) (toSliceTerminal J X K).simplicial
      AddCommGrpCat.{max w u v}).Additive :=
  SemiRepresentableFamily.directImage_additive.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K)

variable [(directImage (J.over X) (toSliceTerminal J X K).simplicial
      AddCommGrpCat.{max w u v}).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (overSiteTotalTopology (J.over X) (toSliceTerminal J X K).simplicial)
        AddCommGrpCat.{max w u v}))]

/-- Bounded-below derived inverse image `a⁻¹` on `D⁺(C / X)`. -/
abbrev plusInverseImageDerived :
    DerivedCategory.Plus (Sheaf (J.over X) AddCommGrpCat.{max w u v}) ⥤
      DerivedCategory.Plus
        (Sheaf (overSiteTotalTopology (J.over X) K.toSimplicialObject)
          AddCommGrpCat.{max w u v}) :=
  SemiRepresentableFamily.plusInverseImageDerived.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K)

/-- Bounded-below derived inverse image is the slice instantiation of the terminal
hypercovering derived inverse image. -/
theorem plusInverseImageDerived_eq :
    plusInverseImageDerived J X K =
      SemiRepresentableFamily.plusInverseImageDerived.{w, v, max u v}
        (J.over X) (toSliceTerminal J X K) :=
  sorry

/-- Bounded-below total right-derived direct image `Ra_*` along `j_total` for a
hypercovering of an object. -/
abbrev plusDirectImageDerived :
    DerivedCategory.Plus
        (Sheaf (overSiteTotalTopology (J.over X) K.toSimplicialObject)
          AddCommGrpCat.{max w u v}) ⥤
      DerivedCategory.Plus (Sheaf (J.over X) AddCommGrpCat.{max w u v}) :=
  SemiRepresentableFamily.plusDirectImageDerived.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K)

/-- Bounded-below `Ra_*` is the slice instantiation of the terminal hypercovering
derived direct image. -/
theorem plusDirectImageDerived_eq :
    plusDirectImageDerived J X K =
      SemiRepresentableFamily.plusDirectImageDerived.{w, v, max u v}
        (J.over X) (toSliceTerminal J X K) :=
  sorry

/-- The bounded-below derived adjunction `a⁻¹ ⊣ Ra_*` attached to a hypercovering of
an object. -/
def plusDerivedAdjunction :
    plusInverseImageDerived J X K ⊣ plusDirectImageDerived J X K :=
  SemiRepresentableFamily.plusDerivedAdjunction.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K)

/-- `plusDerivedAdjunction` is the slice instantiation of the terminal hypercovering
bounded-below derived adjunction. -/
theorem plusDerivedAdjunction_eq :
    plusDerivedAdjunction J X K =
      SemiRepresentableFamily.plusDerivedAdjunction.{w, v, max u v}
        (J.over X) (toSliceTerminal J X K) :=
  sorry

/-- The canonical `D⁺` derived unit `E ⟶ Ra_* a⁻¹ E` on `D⁺(C / X)`. -/
abbrev plusDerivedUnit :
    𝟭 (DerivedCategory.Plus (Sheaf (J.over X) AddCommGrpCat.{max w u v})) ⟶
      plusInverseImageDerived J X K ⋙ plusDirectImageDerived J X K :=
  SemiRepresentableFamily.plusDerivedUnit.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K)

/-- `plusDerivedUnit` is the unit of `plusDerivedAdjunction`. -/
theorem plusDerivedUnit_eq :
    plusDerivedUnit J X K = (plusDerivedAdjunction J X K).unit :=
  sorry

end CategoryTheory.Hypercovering
