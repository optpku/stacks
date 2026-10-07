module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap70.Lemma_70_14_4_Pullback
public import stacks_project.Chap76.Lemma_76_31_1_FiberDimension
public import stacks_project.Chap99.Situation_99_15_1_Category

/-!
# The object property of curves with universally trivial pushforward of 𝒪

`𝒞urves^{h0, 1}` is the full subcategory of families of curves `f : X ⟶ S`
for which `𝒪_S ⟶ f_* 𝒪_X` remains an isomorphism after every base change
and every fibre of `f` has dimension `1`. Membership is the source-facing
packaging of a classifying morphism factoring through that open substack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The object property of families of curves with universally trivial
`𝒪_S ⟶ f_* 𝒪_X` and fibres of dimension `1`, corresponding to the open
substack `𝒞urves^{h0, 1}`. -/
def h0Dim1 (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦
    (∀ {Z : AlgebraicSpace S} (g : Z ⟶ ofOver (base P)),
        IsIso (Modules.unitToPushforwardObjUnit (pullback.snd (hom P) g))) ∧
      ∀ y : Points (ofOver (base P)), fiberDimension (hom P) y = 1

/-- Membership in `h0Dim1` means the unit `𝒪_S ⟶ f_* 𝒪_X` is an isomorphism
after every base change, including the identity, and every fibre has
dimension `1`. -/
theorem h0Dim1_iff {S : Scheme.{u}} (P : Obj S) :
    h0Dim1 S P ↔
      (∀ {Z : AlgebraicSpace S} (g : Z ⟶ ofOver (base P)),
          IsIso (Modules.unitToPushforwardObjUnit (pullback.snd (hom P) g))) ∧
        ∀ y : Points (ofOver (base P)), fiberDimension (hom P) y = 1 :=
  sorry

/-- The `h0Dim1` property of families of curves is closed under isomorphisms. -/
instance instIsClosedUnderIsomorphisms_h0Dim1 (S : Scheme.{u}) :
    (h0Dim1 S).IsClosedUnderIsomorphisms :=
  sorry

/-- The morphism of algebraic spaces over `Spec k` associated to a scheme over
a field. -/
def schemeOverFieldHom {k : Type u} [Field k] (X : SchemeOverField k) :
    ofOver (Over.mk X.hom) ⟶
      ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
  ofOverHomMk X.hom (Category.comp_id X.hom)

/-- `schemeOverFieldHom X` is `ofOverHomMk` of the structure morphism of `X`. -/
theorem schemeOverFieldHom_eq {k : Type u} [Field k] (X : SchemeOverField k) :
    schemeOverFieldHom X =
      ofOverHomMk X.hom (Category.comp_id X.hom) :=
  sorry

/-- A proper scheme over a field is fp-flat-proper as a morphism of algebraic
spaces. -/
instance instFpFlatProper_schemeOverFieldHom {k : Type u} [Field k]
    (X : SchemeOverField k) [IsProper X.hom] :
    FpFlatProper (schemeOverFieldHom X) :=
  sorry

/-- A proper scheme of topological Krull dimension at most one over a field has
relative dimension at most one as a morphism of algebraic spaces. -/
theorem relativeDimensionLE_schemeOverFieldHom {k : Type u} [Field k]
    (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    RelativeDimensionLE (schemeOverFieldHom X) 1 :=
  sorry

/-- Package a proper scheme of topological Krull dimension at most one over a
field as a family of curves over `Spec k`. -/
def mkOfSchemeOverField {k : Type u} [Field k] (X : SchemeOverField k)
    [IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1) :
    Obj (Spec (CommRingCat.of k)) :=
  @mk (Spec (CommRingCat.of k)) (Over.mk (𝟙 (Spec (CommRingCat.of k))))
    (ofOver (Over.mk X.hom)) (schemeOverFieldHom X)
    (instFpFlatProper_schemeOverFieldHom X)
    (relativeDimensionLE_schemeOverFieldHom X hdim)

/-- The structure morphism of `mkOfSchemeOverField X hdim` is
`schemeOverFieldHom X`. -/
theorem mkOfSchemeOverField_hom {k : Type u} [Field k]
    (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    hom (mkOfSchemeOverField X hdim) = schemeOverFieldHom X :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
