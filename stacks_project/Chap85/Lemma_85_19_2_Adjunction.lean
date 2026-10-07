module

public import stacks_project.Chap85.Lemma_85_17_3_Adjunction
public import stacks_project.Chap85.Lemma_85_19_1_Slice

/-!
# Derived adjunction of a hypercovering of an object

If `K` is a hypercovering of an object `X`, the geometric morphism
`a : Sh((C / K)_total) → Sh(C / X)` presented by `j_total` on the slice site
`J.over X` has exact inverse image `a⁻¹` and an additive direct image `a_*`.
This leaf instantiates the unbounded derived functors `a⁻¹` and `Ra_*`, their
derived adjunction, and the canonical unit `E ⟶ Ra_* a⁻¹ E` at
`toSliceTerminal`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SemiRepresentableFamily
  (overSiteDiagram overSiteTotalTopology totalForget inverseImage)
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

/-- The exact inverse-image functor `a⁻¹` on abelian sheaves along `j_total` for a
hypercovering of an object. -/
abbrev inverseImageExact :
    Sheaf (J.over X) AddCommGrpCat.{max w u v} ⥤ₑ
      Sheaf (overSiteTotalTopology (J.over X) K.toSimplicialObject)
        AddCommGrpCat.{max w u v} :=
  SemiRepresentableFamily.inverseImageExact.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K)

/-- The underlying functor of `inverseImageExact` is inverse image along `j_total`. -/
theorem inverseImageExact_obj :
    (inverseImageExact J X K).obj =
      inverseImage (J.over X) K.toSimplicialObject AddCommGrpCat.{max w u v} :=
  sorry

/-- Unbounded derived inverse image `a⁻¹` on `D(C / X)`. -/
abbrev inverseImageDerived :
    DerivedCategory (Sheaf (J.over X) AddCommGrpCat.{max w u v}) ⥤
      DerivedCategory
        (Sheaf (overSiteTotalTopology (J.over X) K.toSimplicialObject)
          AddCommGrpCat.{max w u v}) :=
  SemiRepresentableFamily.inverseImageDerived.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K)

/-- Unbounded derived inverse image is the slice instantiation of the terminal
hypercovering derived inverse image. -/
theorem inverseImageDerived_eq :
    inverseImageDerived J X K =
      SemiRepresentableFamily.inverseImageDerived.{w, v, max u v}
        (J.over X) (toSliceTerminal J X K) :=
  sorry

/-- Unbounded total right-derived direct image `Ra_*` along `j_total` for a
hypercovering of an object. -/
abbrev directImageDerived :
    DerivedCategory
        (Sheaf (overSiteTotalTopology (J.over X) K.toSimplicialObject)
          AddCommGrpCat.{max w u v}) ⥤
      DerivedCategory (Sheaf (J.over X) AddCommGrpCat.{max w u v}) :=
  SemiRepresentableFamily.directImageDerived.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K)

/-- Unbounded `Ra_*` is the slice instantiation of the terminal hypercovering
derived direct image. -/
theorem directImageDerived_eq :
    directImageDerived J X K =
      SemiRepresentableFamily.directImageDerived.{w, v, max u v}
        (J.over X) (toSliceTerminal J X K) :=
  sorry

/-- The unbounded derived adjunction `a⁻¹ ⊣ Ra_*` attached to a hypercovering of an
object. -/
def derivedAdjunction :
    inverseImageDerived J X K ⊣ directImageDerived J X K :=
  SemiRepresentableFamily.derivedAdjunction.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K)

/-- `derivedAdjunction` is the slice instantiation of the terminal hypercovering
derived adjunction. -/
theorem derivedAdjunction_eq :
    derivedAdjunction J X K =
      SemiRepresentableFamily.derivedAdjunction.{w, v, max u v}
        (J.over X) (toSliceTerminal J X K) :=
  sorry

/-- The canonical derived unit `E ⟶ Ra_* a⁻¹ E` on `D(C / X)`. -/
abbrev derivedUnit :
    𝟭 (DerivedCategory (Sheaf (J.over X) AddCommGrpCat.{max w u v})) ⟶
      inverseImageDerived J X K ⋙ directImageDerived J X K :=
  SemiRepresentableFamily.derivedUnit.{w, v, max u v}
    (J.over X) (toSliceTerminal J X K)

/-- `derivedUnit` is the unit of `derivedAdjunction`. -/
theorem derivedUnit_eq :
    derivedUnit J X K = (derivedAdjunction J X K).unit :=
  sorry

end CategoryTheory.Hypercovering
