/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Order.Directed
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap80.Definition_80_3_1_RelativelyRepresentable
public import stacks_project.Chap87.Lemma_87_38_4_Completion

/-!
# Locally weakly adic and locally adic* formal algebraic spaces

Functor-of-points locally weakly adic and locally adic* types, with étale
atlases on the carrier `(Over S)ᵒᵖ ⥤ Type u`. Affine weakly adic charts reuse
`AffineFormalAlgebraicSpace.IsWeaklyAdic`. Formal algebraic space, directed
affine thickening colimit, and locally Noetherian structure are owned here on
the same functor-of-points carrier. These locally adic* classes are distinct
from the sheaf-site predicate `AlgebraicGeometry.IsLocallyAdicStar`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces

/-- The algebraic space `T' = F ×_G T` obtained by pulling a morphism
representable by algebraic spaces back along a Yoneda section. -/
def pullbackSpace {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (ha : representableByAlgebraicSpaces a) {U : Over S} (ξ : yoneda.obj U ⟶ G) :
    AlgebraicSpace S :=
  ofFunctor (pullback ξ a) (ha.isAlgebraicSpace_pullback ξ).isSheaf
    (ha.isAlgebraicSpace_pullback ξ).representableDiagonal
    (ha.isAlgebraicSpace_pullback ξ).atlas

/-- The structure morphism `T' ⟶ T` of the fibre product algebraic space along a
Yoneda section. -/
def pullbackHom {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (ha : representableByAlgebraicSpaces a) {U : Over S} (ξ : yoneda.obj U ⟶ G) :
    pullbackSpace ha ξ ⟶ ofOver U :=
  pullback.fst ξ a

/-- The functor of points of `pullbackSpace ha ξ` is the fibre product of
functors. -/
theorem pullbackSpace_functorOfPoints {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (ha : representableByAlgebraicSpaces a) {U : Over S} (ξ : yoneda.obj U ⟶ G) :
    (pullbackSpace ha ξ).functorOfPoints = pullback ξ a :=
  sorry

/-- The structure morphism of the fibre product algebraic space is the first
projection of the fibre product of functors. -/
theorem pullbackHom_fst {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (ha : representableByAlgebraicSpaces a) {U : Over S} (ξ : yoneda.obj U ⟶ G) :
    pullbackHom ha ξ = pullback.fst ξ a :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces

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
  isAffine_obj : ∀ i, AlgebraicGeometry.IsAffine (D.obj i).left
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

/-- The constant diagram on an affine scheme over `S` is a directed affine
thickening colimit of the corresponding representable functor. -/
instance instConst {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsAffine U.left] :
    IsDirectedAffineThickeningColimit ((Functor.const PUnit.{u + 1}).obj U)
      (yoneda.obj U) :=
  sorry

/-- A directed affine thickening colimit unpacks as affine stages, thickening
transitions, an fppf sheaf, and an fppf-local isomorphism from the Yoneda
presheaf colimit. -/
theorem spec {S : Scheme.{u}} {Λ : Type v} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ Over S) (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsDirectedAffineThickeningColimit D X] :
    (∀ i, AlgebraicGeometry.IsAffine (D.obj i).left) ∧
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
        (∀ i, representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
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
instance instYoneda {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsAffine U.left] :
    IsFormalAlgebraicSpace (yoneda.obj U) :=
  sorry

/-- A functor of points is a formal algebraic space if and only if it is an fppf
sheaf with an étale directed-affine-thickening atlas and a representable
coequalizer presentation. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) X ∧
      (∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
        (∀ i, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
          (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (cover i)) ∧
          (∀ i, representableByAlgebraicSpaces (π i)) ∧
            (∀ i (ha : representableByAlgebraicSpaces (π i))
              {U : Over S} (ξ : yoneda.obj U ⟶ X),
              AlgebraicSpace.Etale
                (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
              Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
                (sigmaDesc π)) ∧
        ∃ (U R : Over S) (πU : yoneda.obj U ⟶ X) (σ : yoneda.obj R ⟶ pullback πU πU),
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ :=
  sorry

end IsFormalAlgebraicSpace

/-- A formal algebraic space over `S` is locally weakly adic when it admits an
étale atlas by weakly adic affine formal algebraic spaces. -/
@[mk_iff]
class IsLocallyWeaklyAdic {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] : Prop where
  /-- There is an étale atlas by weakly adic affine formal algebraic spaces,
  representable by algebraic spaces and jointly fppf-locally surjective. -/
  exists_atlas :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, AffineFormalAlgebraicSpace.IsWeaklyAdic (cover i)) ∧
        (∀ i, representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π)

namespace IsLocallyWeaklyAdic

/-- A locally weakly adic formal algebraic space admits an étale atlas by
weakly adic affine formal algebraic spaces. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyWeaklyAdic X] :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, AffineFormalAlgebraicSpace.IsWeaklyAdic (cover i)) ∧
        (∀ i, representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) :=
  sorry

/-- Locally weakly adic formal algebraic spaces are exactly formal algebraic
spaces with an étale atlas by weakly adic affine charts. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] :
    IsLocallyWeaklyAdic X ↔
      ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
        (∀ i, AffineFormalAlgebraicSpace.IsWeaklyAdic (cover i)) ∧
          (∀ i, representableByAlgebraicSpaces (π i)) ∧
            (∀ i (ha : representableByAlgebraicSpaces (π i))
              {U : Over S} (ξ : yoneda.obj U ⟶ X),
              AlgebraicSpace.Etale
                (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
              Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) :=
  sorry

/-- A weakly adic affine formal algebraic space that is a formal algebraic space
is locally weakly adic. -/
instance ofAffine {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [AffineFormalAlgebraicSpace.IsWeaklyAdic X] :
    IsLocallyWeaklyAdic X :=
  sorry

end IsLocallyWeaklyAdic

/-- An affine formal algebraic space is adic* when it is presented by successive
quotient spectra of an adic ring with a finitely generated ideal of definition. -/
@[mk_iff]
class IsAdicStarAffine {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) : Prop where
  /-- There is an adic ring, a finitely generated ideal of definition, and a
  structure morphism over `S` whose successive quotient spectra present `X`. -/
  exists_adicStar :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : TopologicalRing.IsAdicRing A) (I : Ideal A) (_ : I.FG)
      (_ : TopologicalRing.Ideal.IsIdealOfDefinition I)
      (_ : Spec (.of A) ⟶ S) (D : ℕ ⥤ Over S),
        (∀ n : ℕ,
            Nonempty ((D.obj n).left ≅ Spec (.of (A ⧸ I ^ (n + 1))))) ∧
          IsDirectedAffineThickeningColimit D X

namespace IsAdicStarAffine

/-- The representable functor of an affine scheme over `S` is an adic* affine
formal algebraic space. -/
instance instYoneda {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsAffine U.left] :
    IsAdicStarAffine (yoneda.obj U) :=
  sorry

/-- A functor presented by successive quotient spectra of an adic ring with a
finitely generated ideal of definition is an adic* affine formal algebraic
space. -/
theorem of {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdicRing A] (I : Ideal A) (hI : I.FG)
    (hdef : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (structureHom : Spec (.of A) ⟶ S) (D : ℕ ⥤ Over S)
    (hD : ∀ n : ℕ, Nonempty ((D.obj n).left ≅ Spec (.of (A ⧸ I ^ (n + 1)))))
    (hcolim : IsDirectedAffineThickeningColimit D X) :
    IsAdicStarAffine X :=
  sorry

/-- An adic* affine formal algebraic space is presented by an adic ring with a
finitely generated ideal of definition. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) [IsAdicStarAffine X] :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : TopologicalRing.IsAdicRing A) (I : Ideal A) (_ : I.FG)
      (_ : TopologicalRing.Ideal.IsIdealOfDefinition I)
      (_ : Spec (.of A) ⟶ S) (D : ℕ ⥤ Over S),
        (∀ n : ℕ,
            Nonempty ((D.obj n).left ≅ Spec (.of (A ⧸ I ^ (n + 1))))) ∧
          IsDirectedAffineThickeningColimit D X :=
  sorry

/-- Adic* affine formal algebraic spaces are exactly functors presented by an
adic ring with a finitely generated ideal of definition. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) :
    IsAdicStarAffine X ↔
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : TopologicalRing.IsAdicRing A) (I : Ideal A) (_ : I.FG)
        (_ : TopologicalRing.Ideal.IsIdealOfDefinition I)
        (_ : Spec (.of A) ⟶ S) (D : ℕ ⥤ Over S),
          (∀ n : ℕ,
              Nonempty ((D.obj n).left ≅ Spec (.of (A ⧸ I ^ (n + 1))))) ∧
            IsDirectedAffineThickeningColimit D X :=
  sorry

end IsAdicStarAffine

/-- A formal algebraic space over `S` is locally adic* when it admits an étale
atlas by adic* affine formal algebraic spaces. -/
@[mk_iff]
class IsLocallyAdicStar {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] : Prop where
  /-- There is an étale atlas by adic* affine formal algebraic spaces,
  representable by algebraic spaces and jointly fppf-locally surjective. -/
  exists_atlas :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, IsAdicStarAffine (cover i)) ∧
        (∀ i, representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π)

namespace IsLocallyAdicStar

/-- A locally adic* formal algebraic space admits an étale atlas by adic*
affine formal algebraic spaces. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyAdicStar X] :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, IsAdicStarAffine (cover i)) ∧
        (∀ i, representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) :=
  sorry

/-- Locally adic* formal algebraic spaces are exactly formal algebraic spaces
with an étale atlas by adic* affine charts. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] :
    IsLocallyAdicStar X ↔
      ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
        (∀ i, IsAdicStarAffine (cover i)) ∧
          (∀ i, representableByAlgebraicSpaces (π i)) ∧
            (∀ i (ha : representableByAlgebraicSpaces (π i))
              {U : Over S} (ξ : yoneda.obj U ⟶ X),
              AlgebraicSpace.Etale
                (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
              Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) :=
  sorry

end IsLocallyAdicStar

namespace IsAdicStarAffine

/-- An adic* affine formal algebraic space that is a formal algebraic space is
locally adic*. -/
instance instIsLocallyAdicStar {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsAdicStarAffine X] : IsLocallyAdicStar X :=
  sorry

end IsAdicStarAffine

/-- An affine formal algebraic space is Noetherian when it is presented by
successive quotient spectra of an adic Noetherian topological ring. -/
@[mk_iff]
class IsNoetherianAffine {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) : Prop where
  /-- There is an adic Noetherian topological ring, an ideal of definition, and
  a structure morphism over `S` whose successive quotient spectra present `X`. -/
  exists_adicNoetherian :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : TopologicalRing.IsAdicRing A) (_ : IsNoetherianRing A)
      (I : Ideal A) (_ : TopologicalRing.Ideal.IsIdealOfDefinition I)
      (_ : Spec (.of A) ⟶ S) (D : ℕ ⥤ Over S),
        (∀ n : ℕ,
            Nonempty ((D.obj n).left ≅ Spec (.of (A ⧸ I ^ (n + 1))))) ∧
          IsDirectedAffineThickeningColimit D X

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
      (I : Ideal A) (_ : TopologicalRing.Ideal.IsIdealOfDefinition I)
      (_ : Spec (.of A) ⟶ S) (D : ℕ ⥤ Over S),
        (∀ n : ℕ,
            Nonempty ((D.obj n).left ≅ Spec (.of (A ⧸ I ^ (n + 1))))) ∧
          IsDirectedAffineThickeningColimit D X :=
  sorry

/-- Noetherian affine formal algebraic spaces are exactly functors presented by
an adic Noetherian topological ring. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) :
    IsNoetherianAffine X ↔
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : TopologicalRing.IsAdicRing A) (_ : IsNoetherianRing A)
        (I : Ideal A) (_ : TopologicalRing.Ideal.IsIdealOfDefinition I)
        (_ : Spec (.of A) ⟶ S) (D : ℕ ⥤ Over S),
          (∀ n : ℕ,
              Nonempty ((D.obj n).left ≅ Spec (.of (A ⧸ I ^ (n + 1))))) ∧
            IsDirectedAffineThickeningColimit D X :=
  sorry

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
        (∀ i, representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π)

namespace IsLocallyNoetherian

/-- The representable functor of a Noetherian affine scheme over `S` is a
locally Noetherian formal algebraic space. -/
instance instYoneda {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsAffine U.left] [AlgebraicGeometry.IsNoetherian U.left] :
    IsLocallyNoetherian (yoneda.obj U) :=
  sorry

/-- A locally Noetherian formal algebraic space admits an étale atlas by
Noetherian affine formal algebraic spaces. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, IsNoetherianAffine (cover i)) ∧
        (∀ i, representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) :=
  sorry

/-- Locally Noetherian formal algebraic spaces are exactly formal algebraic
spaces with an étale atlas by Noetherian affine charts. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] :
    IsLocallyNoetherian X ↔
      ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
        (∀ i, IsNoetherianAffine (cover i)) ∧
          (∀ i, representableByAlgebraicSpaces (π i)) ∧
            (∀ i (ha : representableByAlgebraicSpaces (π i))
              {U : Over S} (ξ : yoneda.obj U ⟶ X),
              AlgebraicSpace.Etale
                (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
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

end AlgebraicGeometry.FormalAlgebraicSpace
