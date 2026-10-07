module

public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Definition_67_14_4_IdealSubobject

/-!
# Closed subspaces cut out by ideal sheaves

A quasi-coherent ideal sheaf `I ⊂ 𝒪_X` cuts out a closed subspace of an
algebraic space `X`. Scheme-theoretic intersection and union of closed
subspaces are the closed subspaces cut out by `I ⊔ J` and `I ⊓ J`.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The morphism `ofOver T.unop ⟶ X` determined by a `T`-point of `X`. -/
def homOfPoint {T : (Over S)ᵒᵖ} (h : X.functorOfPoints.obj T) :
    ofOver T.unop ⟶ X :=
  yonedaEquiv.symm h

/-- `homOfPoint` is the Yoneda inverse of a `T`-point. -/
theorem homOfPoint_eq {T : (Over S)ᵒᵖ} (h : X.functorOfPoints.obj T) :
    homOfPoint h = yonedaEquiv.symm h :=
  rfl

/-- The pullback of the inclusion of an ideal sheaf along a morphism of algebraic
spaces. -/
def inclusionPullback {Y : AlgebraicSpace S} (f : Y ⟶ X) (I : IdealSubobject X) :
    (Modules.pullback f).obj I.toModule ⟶
      (Modules.pullback f).obj (SheafOfModules.unit (structureSheaf X)) :=
  (Modules.pullback f).map I.arrow

/-- `inclusionPullback f I` is the image of the subobject arrow of `I` under
module pullback along `f`. -/
theorem inclusionPullback_eq {Y : AlgebraicSpace S} (f : Y ⟶ X)
    (I : IdealSubobject X) :
    inclusionPullback f I = (Modules.pullback f).map I.arrow :=
  rfl

/-- A morphism `f : Y ⟶ X` vanishes on an ideal sheaf `I` when the pulled-back
inclusion `f* I ⟶ f* 𝒪_X` is the zero map. -/
def vanishes {Y : AlgebraicSpace S} (f : Y ⟶ X) (I : IdealSubobject X) : Prop :=
  inclusionPullback f I = 0

/-- Vanishing of `I` along `f` is vanishing of the pulled-back inclusion of `I`. -/
theorem vanishes_iff {Y : AlgebraicSpace S} (f : Y ⟶ X) (I : IdealSubobject X) :
    vanishes f I ↔ inclusionPullback f I = 0 :=
  Iff.rfl

/-- Restriction of a `T`-point along a morphism of test schemes preserves
vanishing of a pulled-back ideal sheaf. -/
theorem vanishes_map {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T') (I : IdealSubobject X)
    {h : X.functorOfPoints.obj T} (hh : vanishes (homOfPoint h) I) :
    vanishes (homOfPoint (X.functorOfPoints.map φ h)) I :=
  sorry

/-- Functor of points of the closed subspace of `X` cut out by an ideal sheaf:
`T`-points are morphisms `T ⟶ X` along which the pulled-back inclusion of the
ideal vanishes. -/
def subschemeFunctor (I : IdealSubobject X) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := {h : X.functorOfPoints.obj T // vanishes (homOfPoint h) I}
  map φ := TypeCat.ofHom fun h => ⟨X.functorOfPoints.map φ h.val, vanishes_map φ I h.property⟩
  map_id := sorry
  map_comp := sorry

/-- The value of `subschemeFunctor I` at a test object is the subtype of points
along which `I` vanishes. -/
theorem subschemeFunctor_obj (I : IdealSubobject X) (T : (Over S)ᵒᵖ) :
    (subschemeFunctor I).obj T =
      {h : X.functorOfPoints.obj T // vanishes (homOfPoint h) I} :=
  rfl

/-- The closed subspace of `X` cut out by a quasi-coherent ideal sheaf. -/
def subscheme (I : IdealSubobject X) [IsQuasiCoherent I] : AlgebraicSpace S :=
  ofFunctor (subschemeFunctor I) sorry sorry sorry

/-- The functor of points of `subscheme I` is `subschemeFunctor I`. -/
@[simp]
theorem subscheme_functorOfPoints (I : IdealSubobject X) [IsQuasiCoherent I] :
    (subscheme I).functorOfPoints = subschemeFunctor I :=
  rfl

/-- The closed-subspace inclusion of the locus cut out by `I` into `X`. -/
def subschemeι (I : IdealSubobject X) [IsQuasiCoherent I] : subscheme I ⟶ X where
  app T := TypeCat.ofHom fun h : (subschemeFunctor I).obj T => h.val
  naturality := sorry

/-- On `T`-points, `subschemeι I` forgets the vanishing witness. -/
theorem subschemeι_app (I : IdealSubobject X) [IsQuasiCoherent I]
    (T : (Over S)ᵒᵖ) (h : (subschemeFunctor I).obj T) :
    (subschemeι I).app T h = h.val :=
  sorry

/-- The inclusion of the closed subspace cut out by `I` is a closed immersion. -/
instance instIsClosedImmersion_subschemeι (I : IdealSubobject X)
    [IsQuasiCoherent I] : IsClosedImmersion (subschemeι I) :=
  sorry

/-- The closed subspace cut out by `I` has functor of points `subschemeFunctor I`,
and its inclusion into `X` is a closed immersion. -/
theorem subscheme_spec (I : IdealSubobject X) [IsQuasiCoherent I] :
    (subscheme I).functorOfPoints = subschemeFunctor I ∧
      IsClosedImmersion (subschemeι I) :=
  sorry

/-- The scheme-theoretic intersection of the closed subspaces cut out by
quasi-coherent ideals `I` and `J` is the closed subspace cut out by `I ⊔ J`. -/
noncomputable abbrev schemeTheoreticIntersection (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] : AlgebraicSpace S :=
  subscheme (I ⊔ J)

/-- Scheme-theoretic intersection is the closed subspace attached to the sum of
ideal sheaves. -/
@[simp]
theorem schemeTheoreticIntersection_eq_subscheme_sup (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    schemeTheoreticIntersection I J = subscheme (I ⊔ J) :=
  rfl

/-- The closed-subspace inclusion of a scheme-theoretic intersection. -/
noncomputable abbrev schemeTheoreticIntersectionι (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    schemeTheoreticIntersection I J ⟶ X :=
  subschemeι (I ⊔ J)

/-- The inclusion of a scheme-theoretic intersection is a closed immersion. -/
instance instIsClosedImmersion_schemeTheoreticIntersectionι (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    IsClosedImmersion (schemeTheoreticIntersectionι I J) :=
  inferInstance

/-- Scheme-theoretic intersection is cut out by `I ⊔ J` and includes as a closed
immersion. -/
theorem schemeTheoreticIntersection_spec (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    schemeTheoreticIntersection I J = subscheme (I ⊔ J) ∧
      IsClosedImmersion (schemeTheoreticIntersectionι I J) :=
  sorry

/-- The scheme-theoretic union of the closed subspaces cut out by quasi-coherent
ideals `I` and `J` is the closed subspace cut out by `I ⊓ J`. -/
noncomputable abbrev schemeTheoreticUnion (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] : AlgebraicSpace S :=
  subscheme (I ⊓ J)

/-- Scheme-theoretic union is the closed subspace attached to the intersection of
ideal sheaves. -/
@[simp]
theorem schemeTheoreticUnion_eq_subscheme_inf (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    schemeTheoreticUnion I J = subscheme (I ⊓ J) :=
  rfl

/-- The closed-subspace inclusion of a scheme-theoretic union. -/
noncomputable abbrev schemeTheoreticUnionι (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    schemeTheoreticUnion I J ⟶ X :=
  subschemeι (I ⊓ J)

/-- The inclusion of a scheme-theoretic union is a closed immersion. -/
instance instIsClosedImmersion_schemeTheoreticUnionι (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    IsClosedImmersion (schemeTheoreticUnionι I J) :=
  inferInstance

/-- Scheme-theoretic union is cut out by `I ⊓ J` and includes as a closed
immersion. -/
theorem schemeTheoreticUnion_spec (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    schemeTheoreticUnion I J = subscheme (I ⊓ J) ∧
      IsClosedImmersion (schemeTheoreticUnionι I J) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
