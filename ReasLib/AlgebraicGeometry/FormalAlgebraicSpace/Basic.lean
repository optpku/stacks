module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Order.Directed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

/-!
# Formal algebraic spaces

The formal-space recognition predicates and the concrete atlas constructions
used to describe them.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u v

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- The pointwise dependent-sum coproduct of a family of functors of points. -/
def sigmaFunctor {S : Scheme.{u}} {ι : Type u} (F : ι → ((Over S)ᵒᵖ ⥤ Type u)) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj T := Σ i : ι, (F i).obj T
  map {T₁ T₂} f := TypeCat.ofHom fun p ↦ ⟨p.1, (F p.1).map f p.2⟩
  map_id := by
    intro T
    apply ConcreteCategory.hom_ext
    intro p
    rcases p with ⟨i, x⟩
    simp
  map_comp := by
    intros T₁ T₂ T₃ f g
    apply ConcreteCategory.hom_ext
    intro p
    rcases p with ⟨i, x⟩
    simp

/-- Evaluating `sigmaFunctor F` gives the corresponding dependent sum. -/
theorem sigmaFunctor_obj {S : Scheme.{u}} {ι : Type u}
    (F : ι → ((Over S)ᵒᵖ ⥤ Type u)) (T : (Over S)ᵒᵖ) :
    (sigmaFunctor F).obj T = Σ i : ι, (F i).obj T :=
  rfl

/-- The copairing of a family of morphisms out of `sigmaFunctor F`. -/
def sigmaDesc {S : Scheme.{u}} {ι : Type u} {F : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    {X : (Over S)ᵒᵖ ⥤ Type u} (π : (i : ι) → F i ⟶ X) :
    sigmaFunctor F ⟶ X where
  app T := TypeCat.ofHom fun p ↦ (π p.1).app T p.2
  naturality := by
    intros T₁ T₂ f
    ext p
    change (π p.1).app T₂ ((F p.1).map f p.2) =
      X.map f ((π p.1).app T₁ p.2)
    exact congrArg (fun h ↦ h p.2) ((π p.1).naturality f)

/-- The copairing evaluates as the corresponding component. -/
theorem sigmaDesc_app {S : Scheme.{u}} {ι : Type u}
    {F : ι → ((Over S)ᵒᵖ ⥤ Type u)} {X : (Over S)ᵒᵖ ⥤ Type u}
    (π : (i : ι) → F i ⟶ X) (T : (Over S)ᵒᵖ) (p : (sigmaFunctor F).obj T) :
    (sigmaDesc π).app T p = (π p.fst).app T p.snd :=
  rfl

/-- A diagram of schemes over `S` is a directed affine thickening colimit of `X`. -/
@[mk_iff]
class IsDirectedAffineThickeningColimit {S : Scheme.{u}} {Λ : Type v} [Preorder Λ]
    [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ Over S) (X : (Over S)ᵒᵖ ⥤ Type u) : Prop where
  /-- Every stage of the diagram is an affine scheme. -/
  isAffine_obj : ∀ i, IsAffine (D.obj i).left
  /-- Every transition of the diagram is a thickening. -/
  isThickening_map : ∀ {i j : Λ} (f : i ⟶ j), IsThickening (D.map f).left
  /-- `X` is a sheaf for the big fppf topology. -/
  isSheaf : Presheaf.IsSheaf (Scheme.fppfTopology.over S) X
  /-- The Yoneda colimit comparison is an fppf-local isomorphism. -/
  exists_colimit :
    ∃ (c : Cocone (D ⋙ yoneda)) (η : c.pt ⟶ X),
      Nonempty (IsColimit c) ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η ∧
          Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η

namespace IsDirectedAffineThickeningColimit

/-- A compatible isomorphism of diagrams preserves the affine thickening presentation. -/
theorem of_iso {S : Scheme.{u}} {Λ : Type v} [Preorder Λ]
    [IsDirected Λ (· ≤ ·)] {D E : Λ ⥤ Over S}
    {X : (Over S)ᵒᵖ ⥤ Type u} (e : D ≅ E)
    (h : IsDirectedAffineThickeningColimit D X) :
    IsDirectedAffineThickeningColimit E X := by
  refine ⟨?_, ?_, h.isSheaf, ?_⟩
  · intro i
    sorry
  · intro i j f
    sorry
  · obtain ⟨c, η, ⟨hc⟩, hsurj, hinj⟩ := h.exists_colimit
    let eYoneda := Functor.isoWhiskerRight e.symm yoneda
    exact ⟨(Cocone.precompose eYoneda.hom).obj c, η,
      ⟨(IsColimit.precomposeHomEquiv eYoneda c).symm hc⟩, hsurj, hinj⟩

/-- The constant `PUnit`-indexed diagram on an affine scheme is a directed affine
thickening colimit of its representable functor. -/
instance instConst {S : Scheme.{u}} (U : Over S) [IsAffine U.left] :
    IsDirectedAffineThickeningColimit ((Functor.const PUnit.{u + 1}).obj U) (yoneda.obj U) :=
  sorry

end IsDirectedAffineThickeningColimit

/-- A sheaf of types on schemes over `S` is a formal algebraic space when it has
an étale atlas by directed affine thickening colimits and a representable presentation. -/
@[mk_iff]
class IsFormalAlgebraicSpace {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) : Prop where
  /-- `X` is a sheaf for the big fppf topology. -/
  isSheaf : Presheaf.IsSheaf (Scheme.fppfTopology.over S) X
  /-- An étale atlas by directed affine thickening colimits. -/
  exists_atlas :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (cover i)) ∧
        (∀ i, AlgebraicSpace.representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : AlgebraicSpace.representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π)
  /-- A representable fppf-locally surjective presentation. -/
  exists_presentation :
    ∃ (U R : Over S) (πU : yoneda.obj U ⟶ X) (σ : yoneda.obj R ⟶ pullback πU πU),
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ

namespace IsFormalAlgebraicSpace

/-- The representable functor of an affine scheme is a formal algebraic space. -/
instance instYoneda {S : Scheme.{u}} (U : Over S) [IsAffine U.left] :
    IsFormalAlgebraicSpace (yoneda.obj U) :=
  sorry

end IsFormalAlgebraicSpace

end AlgebraicGeometry.FormalAlgebraicSpace
