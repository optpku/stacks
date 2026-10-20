module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap66.Definition_66_18_1_Site
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap96.Definition_96_4_1_AssociatedTopology
public import stacks_project.Chap96.Lemma_96_10_1_Comparison

/-!
# Restriction of étale sheaves on a represented groupoid fibration

An algebraic space `F` over `S` determines the tautological functor
`u : F_étale ⥤ (S_F)_étale` sending an étale morphism `φ : ofOver U ⟶ F` to the
corresponding object of the discrete Grothendieck construction of
`F.functorOfPoints`. Precomposition with `u` is the restriction
`ℱ |_{F_étale} = i_F⁻¹ ℱ = π_{F,*} ℱ`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor Opposite
open CategoryTheory.CategoryOfElements
open GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The tautological element of `F.functorOfPoints` at an object of the small
étale site, obtained by Yoneda evaluation of the structure morphism at `𝟙`. -/
def smallEtaleYonedaValue (F : AlgebraicSpace S) (U : smallEtaleSite F) :
    F.functorOfPoints.obj (op U.left) :=
  U.hom.app (op U.left) (𝟙 U.left)

/-- The object of the opposite category of elements of `F.functorOfPoints`
associated to an étale morphism into `F`. -/
def smallEtaleToGroupoidsObj (F : AlgebraicSpace S) (U : smallEtaleSite F) :
    F.functorOfPoints.Elementsᵒᵖ :=
  op ⟨op U.left, smallEtaleYonedaValue F U⟩

/-- Triangle identity for the structure morphisms of a map in the small étale
site, after evaluating at the identity of the source. -/
theorem smallEtaleYonedaValue_map (F : AlgebraicSpace S)
    {U V : smallEtaleSite F} (f : U ⟶ V) :
    F.functorOfPoints.map f.left.op (smallEtaleYonedaValue F V) =
      smallEtaleYonedaValue F U :=
  sorry

/-- The morphism in the opposite category of elements induced by a morphism of
the small étale site. -/
def smallEtaleToGroupoidsMap (F : AlgebraicSpace S) {U V : smallEtaleSite F}
    (f : U ⟶ V) :
    smallEtaleToGroupoidsObj F U ⟶ smallEtaleToGroupoidsObj F V :=
  (homMk (unop (smallEtaleToGroupoidsObj F V)) (unop (smallEtaleToGroupoidsObj F U))
      f.left.op (smallEtaleYonedaValue_map F f)).op

/-- The tautological functor `u : F_étale ⥤ (S_F)_étale` of lemma-compare,
identified with `GroupoidsOver.smallEtaleToGroupoids` so that type-valued
restriction and module restriction `π_{F,*}` use the same functor. -/
abbrev smallEtaleToGroupoids (F : AlgebraicSpace S) :
    smallEtaleSite F ⥤ F.toGroupoids.total :=
  GroupoidsOver.smallEtaleToGroupoids F

/-- `smallEtaleToGroupoids` is the comparison functor of lemma-compare. -/
theorem smallEtaleToGroupoids_eq (F : AlgebraicSpace S) :
    smallEtaleToGroupoids F = GroupoidsOver.smallEtaleToGroupoids F :=
  rfl

/-- The object map of `smallEtaleToGroupoids` is the tautological category-of-elements
object of the structure morphism. -/
theorem smallEtaleToGroupoids_obj (F : AlgebraicSpace S) (U : smallEtaleSite F) :
    (smallEtaleToGroupoids F).obj U = GroupoidsOver.toGroupoidsObj U :=
  rfl

/-- The morphism map of `smallEtaleToGroupoids` is the opposite category-of-elements
morphism of the underlying map in `Over S`. -/
theorem smallEtaleToGroupoids_map (F : AlgebraicSpace S) {U V : smallEtaleSite F}
    (f : U ⟶ V) :
    (smallEtaleToGroupoids F).map f = GroupoidsOver.toGroupoidsMap f :=
  rfl

/-- Yoneda evaluation at `𝟙` recovers the object map of `smallEtaleToGroupoids`. -/
theorem smallEtaleToGroupoids_obj_yoneda (F : AlgebraicSpace S)
    (U : smallEtaleSite F) :
    (smallEtaleToGroupoids F).obj U = smallEtaleToGroupoidsObj F U :=
  sorry

/-- The tautological functor `u : F_étale ⥤ (S_F)_étale` is continuous for the
small étale topology of `F` and the associated étale topology of `S_F`. -/
instance smallEtaleToGroupoids_isContinuous (F : AlgebraicSpace S) :
    (smallEtaleToGroupoids F).IsContinuous
      (smallEtaleTopology F) F.toGroupoids.etaleTopology :=
  sorry

/-- The tautological functor `u : F_étale ⥤ (S_F)_étale` is cocontinuous for the
small étale topology of `F` and the associated étale topology of `S_F`. -/
instance smallEtaleToGroupoids_isCocontinuous (F : AlgebraicSpace S) :
    (smallEtaleToGroupoids F).IsCocontinuous
      (smallEtaleTopology F) F.toGroupoids.etaleTopology :=
  sorry

/-- Restriction of an étale sheaf on `S_F` to the small étale site of `F`,
i.e. `ℱ |_{F_étale} = i_F⁻¹ ℱ = π_{F,*} ℱ`. -/
def restrictEtale (F : AlgebraicSpace S) :
    Sheaf F.toGroupoids.etaleTopology (Type (u + 1)) ⥤
      Sheaf (smallEtaleTopology F) (Type (u + 1)) :=
  (smallEtaleToGroupoids F).sheafPushforwardContinuous (Type (u + 1))
    (smallEtaleTopology F) F.toGroupoids.etaleTopology

/-- `restrictEtale` is continuous sheaf pushforward along `smallEtaleToGroupoids`. -/
theorem restrictEtale_eq (F : AlgebraicSpace S) :
    restrictEtale F =
      (smallEtaleToGroupoids F).sheafPushforwardContinuous (Type (u + 1))
        (smallEtaleTopology F) F.toGroupoids.etaleTopology :=
  rfl

/-- Sections of a restricted sheaf on `F_étale` are the original sections on the
tautological object `u(U)`. -/
theorem restrictEtale_obj (F : AlgebraicSpace S)
    (ℱ : Sheaf F.toGroupoids.etaleTopology (Type (u + 1)))
    (U : smallEtaleSite F) :
    ((restrictEtale F).obj ℱ).obj.obj (op U) =
      ℱ.obj.obj (op ((smallEtaleToGroupoids F).obj U)) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
