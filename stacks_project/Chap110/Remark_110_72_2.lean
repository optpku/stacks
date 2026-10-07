module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap78.Definition_78_8_1_Action
public import stacks_project.Chap78.Definition_78_9_3_Torsor
public import stacks_project.Chap110.Lemma_110_72_1

/-!
# Fppf torsor sections and H¹ over regular bases, without a dimension hypothesis
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open scoped CategoryTheory.MonObj

noncomputable section

namespace AlgebraicGeometry.GroupScheme

/-- The morphism of algebraic spaces over `W` induced by
`W.fromSpecStalk (genericPoint W)`. -/
def genericPointAsAlgebraicSpace (W : Scheme.{u}) [IsIntegral W] :
    ofOver (Over.mk (W.fromSpecStalk (genericPoint W))) ⟶
      ofOver (Over.mk (𝟙 W)) :=
  ofOverHomMk (W.fromSpecStalk (genericPoint W))
    (Category.comp_id (W.fromSpecStalk (genericPoint W)))

/-- Unfolding `genericPointAsAlgebraicSpace` recovers `ofOverHomMk` of
`W.fromSpecStalk (genericPoint W)`. -/
theorem genericPointAsAlgebraicSpace_eq (W : Scheme.{u}) [IsIntegral W] :
    genericPointAsAlgebraicSpace W =
      ofOverHomMk (W.fromSpecStalk (genericPoint W))
        (Category.comp_id (W.fromSpecStalk (genericPoint W))) :=
  sorry

/-- The generic point of an integral scheme `W`, as a morphism in the slice of
algebraic spaces over `ofOver (Over.mk (𝟙 W))`. -/
def genericPointOver (W : Scheme.{u}) [IsIntegral W] :
    Over.mk (genericPointAsAlgebraicSpace W) ⟶
      Over.mk (𝟙 (ofOver (Over.mk (𝟙 W)))) :=
  Over.homMk (genericPointAsAlgebraicSpace W)

/-- `genericPointOver W` is the slice morphism associated to
`genericPointAsAlgebraicSpace W`. -/
theorem genericPointOver_eq (W : Scheme.{u}) [IsIntegral W] :
    genericPointOver W = Over.homMk (genericPointAsAlgebraicSpace W) :=
  sorry

/-- Restriction of sections of an algebraic space `Y` over `W` along
`W.fromSpecStalk (genericPoint W)`, as precomposition in the slice over
`ofOver (Over.mk (𝟙 W))`. -/
def sectionsRestrictFunctionField {W : Scheme.{u}} [IsIntegral W]
    (Y : Over (ofOver (Over.mk (𝟙 W)))) :
    (Over.mk (𝟙 (ofOver (Over.mk (𝟙 W)))) ⟶ Y) →
      (Over.mk (genericPointAsAlgebraicSpace W) ⟶ Y) :=
  fun s ↦ genericPointOver W ≫ s

/-- Unfolding `sectionsRestrictFunctionField` recovers precomposition with
`Over.homMk (genericPointAsAlgebraicSpace W)`. -/
theorem sectionsRestrictFunctionField_apply {W : Scheme.{u}} [IsIntegral W]
    {Y : Over (ofOver (Over.mk (𝟙 W)))}
    (s : Over.mk (𝟙 (ofOver (Over.mk (𝟙 W)))) ⟶ Y) :
    sectionsRestrictFunctionField Y s =
      Over.homMk (genericPointAsAlgebraicSpace W) ≫ s :=
  sorry

/-- Remark 110.72.2 (1): if `W` is Noetherian, regular, and integral and `G` is
an abelian scheme over `W`, then for every fppf `G`-torsor `P` in algebraic
spaces the restriction `sectionsRestrictFunctionField P.X` from sections over
`W` to sections over `Spec W.functionField` is bijective. -/
@[stacks 0H8E]
theorem sectionsRestrictFunctionField_bijective {W : Scheme.{u}}
    [IsIntegral W] [IsNoetherian W] [Scheme.Regular W]
    (G : GroupScheme W) [AbelianScheme G]
    (P : GroupAlgebraicSpace.Action (toGroupAlgebraicSpace G))
    (hP : GroupAlgebraicSpace.IsStandardTorsor (toGroupAlgebraicSpace G) P .fppf) :
    Function.Bijective (sectionsRestrictFunctionField P.X) :=
  sorry

/-- Remark 110.72.2 (2): if `W` is Noetherian, regular, and integral and `G` is
an abelian scheme over `W`, then the restriction
`fppfH1RestrictFunctionField G` from fppf H¹ of `G` over `W` to fppf H¹ of `G`
over `Spec W.functionField` is injective. -/
@[stacks 0H8E]
theorem fppfH1RestrictFunctionField_injective_regular {W : Scheme.{u}}
    [IsIntegral W] [IsNoetherian W] [Scheme.Regular W]
    (G : GroupScheme W) [AbelianScheme G]
    [HasSheafify (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left)
        AddCommGrpCat.{u})] :
    Function.Injective (fppfH1RestrictFunctionField G).hom :=
  sorry

/-- Remark 110.72.2 (3): the bijectivity of `sectionsRestrictFunctionField` on
fppf `G`-torsors in algebraic spaces remains valid after replacing regularity
of `W` by the assumption that every smooth `W`-scheme is locally factorial. -/
@[stacks 0H8E]
theorem sectionsRestrictFunctionField_bijective_of_smoothLocallyFactorial
    {W : Scheme.{u}} [IsIntegral W] [IsNoetherian W]
    (h_smoothLocallyFactorial :
      ∀ {X : Scheme.{u}} (f : X ⟶ W) [Smooth f] (x : X),
        UniqueFactorizationMonoid (X.presheaf.stalk x))
    (G : GroupScheme W) [AbelianScheme G]
    (P : GroupAlgebraicSpace.Action (toGroupAlgebraicSpace G))
    (hP : GroupAlgebraicSpace.IsStandardTorsor (toGroupAlgebraicSpace G) P .fppf) :
    Function.Bijective (sectionsRestrictFunctionField P.X) :=
  sorry

/-- Injectivity of `fppfH1RestrictFunctionField` under the locally factorial
weakening of regularity, as (2) follows from (1). -/
theorem fppfH1RestrictFunctionField_injective_of_smoothLocallyFactorial
    {W : Scheme.{u}} [IsIntegral W] [IsNoetherian W]
    (h_smoothLocallyFactorial :
      ∀ {X : Scheme.{u}} (f : X ⟶ W) [Smooth f] (x : X),
        UniqueFactorizationMonoid (X.presheaf.stalk x))
    (G : GroupScheme W) [AbelianScheme G]
    [HasSheafify (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left)
        AddCommGrpCat.{u})] :
    Function.Injective (fppfH1RestrictFunctionField G).hom :=
  sorry

end AlgebraicGeometry.GroupScheme
