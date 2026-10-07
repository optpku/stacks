module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.FormalSpace.AdicDiagram
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Order.Directed
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.RingTheory.Topology.Adic.Complete
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap80.Lemma_80_4_6

/-!
# Formal algebraic spaces over a scheme

A sheaf on schemes over `S` is a formal algebraic space when it admits an étale
atlas by directed affine thickening colimits in the fppf sheaf category, the
atlas maps are representable by algebraic spaces, and it is a coequalizer of
representable sheaves. Locally
Noetherian objects are those with an étale atlas by Noetherian affine formal
algebraic spaces, presented by adic Noetherian topological rings. Locally of
finite type morphisms are recorded as unbundled properties on the same
functor-of-points category.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u v

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- The pointwise dependent-sum coproduct of a family of functors of points on
schemes over `S`. -/
def sigmaFunctor {S : Scheme.{u}} {ι : Type u} (F : ι → ((Over S)ᵒᵖ ⥤ Type u)) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj T := Σ i : ι, (F i).obj T
  map {T₁ T₂} (f : T₁ ⟶ T₂) :=
    TypeCat.ofHom fun (p : Σ i : ι, (F i).obj T₁) ↦
      ⟨p.1, (F p.1).map f p.2⟩
  map_id := sorry
  map_comp := sorry

/-- Evaluating `sigmaFunctor F` at `T` is the dependent sum of the values of `F`. -/
theorem sigmaFunctor_obj {S : Scheme.{u}} {ι : Type u} (F : ι → ((Over S)ᵒᵖ ⥤ Type u))
    (T : (Over S)ᵒᵖ) :
    (sigmaFunctor F).obj T = Σ i : ι, (F i).obj T :=
  sorry

/-- The copairing of a family of morphisms out of `sigmaFunctor F`. -/
def sigmaDesc {S : Scheme.{u}} {ι : Type u} {F : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    {X : (Over S)ᵒᵖ ⥤ Type u} (π : (i : ι) → F i ⟶ X) :
    sigmaFunctor F ⟶ X where
  app T :=
    TypeCat.ofHom fun (p : (sigmaFunctor F).obj T) ↦ (π p.1).app T p.2
  naturality := sorry

/-- The copairing of a family of morphisms evaluates as the corresponding component. -/
theorem sigmaDesc_app {S : Scheme.{u}} {ι : Type u} {F : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    {X : (Over S)ᵒᵖ ⥤ Type u} (π : (i : ι) → F i ⟶ X) (T : (Over S)ᵒᵖ)
    (p : (sigmaFunctor F).obj T) :
    (sigmaDesc π).app T p = (π p.fst).app T p.snd :=
  sorry

/-- A diagram of schemes over `S` is a directed affine thickening colimit of `X`
when its objects are affine, its transitions are thickenings, `X` is an fppf
sheaf, and the comparison map from the Yoneda presheaf colimit of the diagram
to `X` is an fppf-local isomorphism. -/
@[mk_iff]
class IsDirectedAffineThickeningColimit {S : Scheme.{u}} {Λ : Type v} [Preorder Λ]
    [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ Over S) (X : (Over S)ᵒᵖ ⥤ Type u) : Prop where
  /-- Every stage of the diagram is an affine scheme. -/
  isAffine_obj : ∀ i, IsAffine (D.obj i).left
  /-- Every transition of the diagram is a thickening. -/
  isThickening_map : ∀ {i j : Λ} (f : i ⟶ j), IsThickening (D.map f).left
  /-- `X` is a sheaf for the big fppf topology on `Over S`. -/
  isSheaf : Presheaf.IsSheaf (Scheme.fppfTopology.over S) X
  /-- The comparison from the Yoneda presheaf colimit of `D` to `X` is an
  fppf-local isomorphism. -/
  exists_colimit :
    ∃ (c : Cocone (D ⋙ yoneda)) (η : c.pt ⟶ X),
      Nonempty (IsColimit c) ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η ∧
          Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η

namespace IsDirectedAffineThickeningColimit

/-- The constant `ℕ`-diagram on an affine scheme over `S` is a directed affine
thickening colimit of the corresponding representable functor. -/
instance instConst {S : Scheme.{u}} (U : Over S) [IsAffine U.left] :
    IsDirectedAffineThickeningColimit ((Functor.const PUnit.{u + 1}).obj U) (yoneda.obj U) :=
  sorry

/-- A directed affine thickening colimit unpacks as affine stages, thickening
transitions, an fppf sheaf, and an fppf-local isomorphism from the Yoneda
presheaf colimit. -/
theorem spec {S : Scheme.{u}} {Λ : Type v} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ Over S) (X : (Over S)ᵒᵖ ⥤ Type u) [IsDirectedAffineThickeningColimit D X] :
    (∀ i, IsAffine (D.obj i).left) ∧
      (∀ {i j : Λ} (f : i ⟶ j), IsThickening (D.map f).left) ∧
        Presheaf.IsSheaf (Scheme.fppfTopology.over S) X ∧
          ∃ (c : Cocone (D ⋙ yoneda)) (η : c.pt ⟶ X),
            Nonempty (IsColimit c) ∧
              Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η ∧
                Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η :=
  sorry

end IsDirectedAffineThickeningColimit

/-- A sheaf of types on schemes over `S` is a formal algebraic space when it
admits a jointly fppf-locally surjective étale atlas by directed affine
thickening colimits, with atlas maps representable by algebraic spaces, and is a
coequalizer of two maps of representable sheaves. -/
@[mk_iff]
class IsFormalAlgebraicSpace {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) : Prop where
  /-- `X` is a sheaf for the big fppf topology on `Over S`. -/
  isSheaf : Presheaf.IsSheaf (Scheme.fppfTopology.over S) X
  /-- There is an étale atlas by directed affine thickening colimits, representable
  by algebraic spaces and jointly fppf-locally surjective. -/
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
  /-- There exist schemes `U`, `R` over `S` with fppf-locally surjective maps
  `yoneda.obj U ⟶ X` and `yoneda.obj R ⟶ U ×_X U`. -/
  exists_presentation :
    ∃ (U R : Over S) (πU : yoneda.obj U ⟶ X) (σ : yoneda.obj R ⟶ pullback πU πU),
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ

namespace IsFormalAlgebraicSpace

/-- The representable functor of an affine scheme over `S` is a formal algebraic
space. -/
instance instYoneda {S : Scheme.{u}} (U : Over S) [IsAffine U.left] :
    IsFormalAlgebraicSpace (yoneda.obj U) :=
  sorry

/-- A functor of points is a formal algebraic space if and only if it is an fppf
sheaf with an étale directed-affine-thickening atlas and a representable
coequalizer presentation. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X] :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) X ∧
      (∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
        (∀ i, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
          (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (cover i)) ∧
          (∀ i, AlgebraicSpace.representableByAlgebraicSpaces (π i)) ∧
            (∀ i (ha : AlgebraicSpace.representableByAlgebraicSpaces (π i))
              {U : Over S} (ξ : yoneda.obj U ⟶ X),
              AlgebraicSpace.Etale
                (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
              Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π)) ∧
        ∃ (U R : Over S) (πU : yoneda.obj U ⟶ X) (σ : yoneda.obj R ⟶ pullback πU πU),
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ :=
  sorry

end IsFormalAlgebraicSpace

/-- An affine formal algebraic space is Noetherian when it is presented by
successive quotient spectra of an adic Noetherian topological ring. -/
@[mk_iff]
class IsNoetherianAffine {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) : Prop where
  /-- There is an adic Noetherian topological ring, an ideal of definition, and
  a structure morphism over `S` whose actual quotient diagram over `S` presents `X`. The transition maps and
  all structure maps are fixed by `AdicPresentation.diagram`; unrelated
  pointwise scheme isomorphisms are not a presentation. -/
  exists_adicNoetherian :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : TopologicalRing.IsAdicRing A) (_ : IsNoetherianRing A)
      (I : Ideal A) (_ : IsAdic I ∧ IsAdicComplete I A)
      (hA : Spec (.of A) ⟶ S),
        IsDirectedAffineThickeningColimit (AdicPresentation.diagram hA I) X

namespace IsNoetherianAffine

/-- The representable functor of a Noetherian affine scheme over `S` is a
Noetherian affine formal algebraic space. -/
instance instYoneda {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsAffine U.left] [AlgebraicGeometry.IsNoetherian U.left] :
    IsNoetherianAffine (yoneda.obj U) :=
  sorry

/-- A Noetherian affine formal algebraic space is presented by an adic
Noetherian topological ring. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) [IsNoetherianAffine X] :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : TopologicalRing.IsAdicRing A) (_ : IsNoetherianRing A)
      (I : Ideal A) (_ : IsAdic I ∧ IsAdicComplete I A)
      (hA : Spec (.of A) ⟶ S),
        IsDirectedAffineThickeningColimit (AdicPresentation.diagram hA I) X :=
  ‹IsNoetherianAffine X›.exists_adicNoetherian

/-- Noetherian affine formal algebraic spaces are exactly functors presented by
an adic Noetherian topological ring. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) :
    IsNoetherianAffine X ↔
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : TopologicalRing.IsAdicRing A) (_ : IsNoetherianRing A)
        (I : Ideal A) (_ : IsAdic I ∧ IsAdicComplete I A)
        (hA : Spec (.of A) ⟶ S),
        IsDirectedAffineThickeningColimit (AdicPresentation.diagram hA I) X :=
  ⟨fun h ↦ h.exists_adicNoetherian, fun h ↦ ⟨h⟩⟩

end IsNoetherianAffine

/-- A formal algebraic space over `S` is locally Noetherian when it admits an
étale atlas by Noetherian affine formal algebraic spaces. -/
@[mk_iff]
class IsLocallyNoetherian {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] : Prop where
  /-- There is an étale atlas by Noetherian affine formal algebraic spaces,
  representable by algebraic spaces and jointly fppf-locally surjective. -/
  exists_noetherian_atlas :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, IsNoetherianAffine (cover i)) ∧
        (∀ i, AlgebraicSpace.representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : AlgebraicSpace.representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π)

namespace IsLocallyNoetherian

/-- The representable functor of a Noetherian affine scheme over `S` is a
locally Noetherian formal algebraic space. -/
instance instYoneda {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsAffine U.left] [AlgebraicGeometry.IsNoetherian U.left] :
    FormalAlgebraicSpace.IsLocallyNoetherian (yoneda.obj U) :=
  sorry

/-- A locally Noetherian formal algebraic space admits an étale atlas by
Noetherian affine formal algebraic spaces. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, IsNoetherianAffine (cover i)) ∧
        (∀ i, AlgebraicSpace.representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : AlgebraicSpace.representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) :=
  sorry

end IsLocallyNoetherian

namespace IsNoetherianAffine

/-- A Noetherian affine formal algebraic space that is a formal algebraic space
is locally Noetherian. -/
instance instIsLocallyNoetherian {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsNoetherianAffine X] : IsLocallyNoetherian X :=
  sorry

end IsNoetherianAffine

/-- A morphism of functors of points on schemes over `S` is locally of finite type
when it is representable by algebraic spaces and every Yoneda pullback is locally
of finite type as a morphism of algebraic spaces. -/
@[mk_iff]
class LocallyOfFiniteType {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) : Prop where
  /-- `f` is representable by algebraic spaces. -/
  representable : AlgebraicSpace.representableByAlgebraicSpaces f
  /-- Every Yoneda pullback of `f` is locally of finite type. -/
  of_pullback :
    ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
      AlgebraicSpace.LocallyOfFiniteType
        (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom representable ξ)

namespace LocallyOfFiniteType

/-- The identity morphism of a functor of points is locally of finite type. -/
instance id {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} : LocallyOfFiniteType (𝟙 X) :=
  sorry

/-- A morphism is locally of finite type if and only if it is representable by
algebraic spaces and every Yoneda pullback is locally of finite type. -/
theorem spec {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    [hf : LocallyOfFiniteType f] :
    AlgebraicSpace.representableByAlgebraicSpaces f ∧
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
        AlgebraicSpace.LocallyOfFiniteType
          (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom hf.representable ξ) :=
  sorry

end LocallyOfFiniteType

end AlgebraicGeometry.FormalAlgebraicSpace
