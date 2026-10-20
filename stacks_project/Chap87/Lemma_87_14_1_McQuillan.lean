/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Directed
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import stacks_project.Chap87.Lemma_87_14_1_Completion
public import stacks_project.Chap87.Lemma_87_38_5_Types

/-!
# McQuillan affine formal algebraic spaces, functor of points

An affine formal algebraic space given as a functor of points
`(Over S)ᵒᵖ ⥤ Type u` is McQuillan when some directed affine thickening
presentation has surjective inverse-limit projections on global sections.
The ideals `J` with `V(J) = T` present the completion of `Spec(A)` along
`T` in this way.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FormalAlgebraicSpace Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- The inverse-limit projections on global sections of a diagram of schemes
over `S` are surjective: every global section of a stage extends to a
compatible family. -/
def IsSurjectiveLimitGlobalSections {S : Scheme.{u}} {Λ : Type u} [Preorder Λ]
    (D : Λ ⥤ Over S) : Prop :=
  ∀ (i : Λ) (x : (Γ((D.obj i).left, ⊤) : Type u)),
    ∃ s : (j : Λ) → (Γ((D.obj j).left, ⊤) : Type u),
      (∀ {j k : Λ} (f : j ⟶ k), (D.map f).left.appTop (s k) = s j) ∧ s i = x

/-- Unfold surjectivity of inverse-limit projections on global sections as
existence of compatible families of sections. -/
theorem isSurjectiveLimitGlobalSections_iff {S : Scheme.{u}} {Λ : Type u}
    [Preorder Λ] (D : Λ ⥤ Over S) :
    IsSurjectiveLimitGlobalSections D ↔
      ∀ (i : Λ) (x : (Γ((D.obj i).left, ⊤) : Type u)),
        ∃ s : (j : Λ) → (Γ((D.obj j).left, ⊤) : Type u),
          (∀ {j k : Λ} (f : j ⟶ k), (D.map f).left.appTop (s k) = s j) ∧
            s i = x :=
  sorry

/-- An affine formal algebraic space, as a functor of points on `Over S`, is
McQuillan when some directed affine thickening presentation has surjective
inverse-limit projections on global sections. -/
@[mk_iff]
class IsMcQuillanAffine {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) : Prop where
  /-- There is a directed affine thickening presentation whose inverse-limit
  projections on global sections are surjective. -/
  exists_surjective_limit_colimit :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      IsDirectedAffineThickeningColimit D X ∧ IsSurjectiveLimitGlobalSections D

namespace IsMcQuillanAffine

/-- Exhibit a McQuillan affine formal algebraic space by a directed thickening
presentation with surjective inverse-limit projections on global sections. -/
theorem of {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} {Λ : Type u}
    [Preorder Λ] [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ Over S)
    (hcolim : IsDirectedAffineThickeningColimit D X)
    (hlim : IsSurjectiveLimitGlobalSections D) : IsMcQuillanAffine X :=
  sorry

/-- A McQuillan affine formal algebraic space admits a directed thickening
presentation with surjective inverse-limit projections on global sections. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) [IsMcQuillanAffine X] :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      IsDirectedAffineThickeningColimit D X ∧ IsSurjectiveLimitGlobalSections D :=
  sorry

/-- A functor of points is a McQuillan affine formal algebraic space if and
only if some directed affine thickening presentation has surjective
inverse-limit projections on global sections. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) :
    IsMcQuillanAffine X ↔
      ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
        IsDirectedAffineThickeningColimit D X ∧
          IsSurjectiveLimitGlobalSections D :=
  sorry

/-- The representable functor of an affine scheme over `S` is a McQuillan
affine formal algebraic space, via the constant directed system. -/
instance instYoneda {S : Scheme.{u}} (U : Over S) [IsAffine U.left] :
    IsMcQuillanAffine (yoneda.obj U) :=
  sorry

/-- A McQuillan affine formal algebraic space is a formal algebraic space. -/
instance instIsFormalAlgebraicSpace {S : Scheme.{u}}
    (X : (Over S)ᵒᵖ ⥤ Type u) [IsMcQuillanAffine X] :
    IsFormalAlgebraicSpace X :=
  sorry

end IsMcQuillanAffine

/-- Ideals `J ⊆ A` with `V(J) = T`, as an index type for the directed system
`Spec(A ⧸ J)`. -/
def IdealCuttingOut {A : Type u} [CommRing A] (T : Closeds (Spec (.of A))) :
    Type u :=
  { J : Ideal A // T = zeroLocusCloseds J }

/-- Bundle an ideal with a proof that its zero locus is `T`. -/
def IdealCuttingOut.of {A : Type u} [CommRing A] {T : Closeds (Spec (.of A))}
    (J : Ideal A) (hJ : T = zeroLocusCloseds J) : IdealCuttingOut T :=
  ⟨J, hJ⟩

/-- The smart constructor recovers the underlying ideal and the zero-locus
condition. -/
theorem IdealCuttingOut.of_spec {A : Type u} [CommRing A]
    {T : Closeds (Spec (.of A))} (J : Ideal A)
    (hJ : T = zeroLocusCloseds J) :
    (IdealCuttingOut.of J hJ).val = J ∧
      T = zeroLocusCloseds (IdealCuttingOut.of J hJ).val :=
  sorry

/-- An index in `IdealCuttingOut T` is an ideal whose zero locus is `T`. -/
theorem IdealCuttingOut.spec {A : Type u} [CommRing A]
    {T : Closeds (Spec (.of A))} (J : IdealCuttingOut T) :
    T = zeroLocusCloseds J.val :=
  sorry

/-- Reverse inclusion of underlying ideals, so that `J ⟶ K` yields
`Spec(A ⧸ J) ⟶ Spec(A ⧸ K)`. -/
instance {A : Type u} [CommRing A] (T : Closeds (Spec (.of A))) :
    Preorder (IdealCuttingOut T) where
  le J K := K.val ≤ J.val
  le_refl := sorry
  le_trans := sorry

/-- Reverse inclusion unpacks as inclusion of underlying ideals. -/
theorem IdealCuttingOut.le_iff {A : Type u} [CommRing A]
    {T : Closeds (Spec (.of A))} {J K : IdealCuttingOut T} :
    J ≤ K ↔ K.val ≤ J.val :=
  sorry

/-- The reverse-inclusion order on ideals cutting out `T` is directed. -/
instance {A : Type u} [CommRing A] (T : Closeds (Spec (.of A))) :
    IsDirected (IdealCuttingOut T) (· ≤ ·) :=
  sorry

/-- The affine stage `Spec(A ⧸ J)` over `S`. -/
def idealStage {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) {T : Closeds (Spec (.of A))}
    (J : IdealCuttingOut T) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.val)) ≫ structureHom)

/-- The underlying scheme of `idealStage structureHom J` is `Spec(A ⧸ J)`. -/
theorem idealStage_left {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) {T : Closeds (Spec (.of A))}
    (J : IdealCuttingOut T) :
    (idealStage structureHom J).left = Spec (.of (A ⧸ J.val)) :=
  sorry

/-- Each ideal stage is affine. -/
instance idealStage_isAffine {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) {T : Closeds (Spec (.of A))}
    (J : IdealCuttingOut T) : IsAffine (idealStage structureHom J).left :=
  sorry

/-- The morphism of schemes over `S` from an ideal stage to `Spec(A)`. -/
def idealStageToSpec {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) {T : Closeds (Spec (.of A))}
    (J : IdealCuttingOut T) :
    idealStage structureHom J ⟶ Over.mk structureHom :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.val))) rfl

/-- The underlying scheme morphism of `idealStageToSpec` is `Spec` of the
quotient map `A →+* A ⧸ J`. -/
theorem idealStageToSpec_left {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) {T : Closeds (Spec (.of A))}
    (J : IdealCuttingOut T) :
    (idealStageToSpec structureHom J).left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.val)) :=
  sorry

/-- The diagram of affine thickenings `Spec(A ⧸ J)` indexed by ideals with
zero locus `T`. -/
def idealThickenings {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (T : Closeds (Spec (.of A))) :
    IdealCuttingOut T ⥤ Over S where
  obj J := idealStage structureHom J
  map {J K} f :=
    Over.homMk
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor (leOfHom f : K.val ≤ J.val))))
      sorry
  map_id := sorry
  map_comp := sorry

/-- Objects of `idealThickenings structureHom T` are the stages
`idealStage structureHom J`. -/
theorem idealThickenings_obj {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (T : Closeds (Spec (.of A)))
    (J : IdealCuttingOut T) :
    (idealThickenings structureHom T).obj J = idealStage structureHom J :=
  sorry

/-- Transition maps of `idealThickenings structureHom T` are thickenings. -/
instance idealThickenings_map_isThickening {S : Scheme.{u}} {A : Type u}
    [CommRing A] (structureHom : Spec (.of A) ⟶ S)
    (T : Closeds (Spec (.of A))) {J K : IdealCuttingOut T} (f : J ⟶ K) :
    IsThickening ((idealThickenings structureHom T).map f).left :=
  sorry

/-- The ideal-stage diagram presents the completion of `Spec(A)` along `T` as a
directed affine thickening colimit. -/
instance isDirectedAffineThickeningColimit_idealThickenings {S : Scheme.{u}}
    {A : Type u} [CommRing A] (structureHom : Spec (.of A) ⟶ S)
    (T : Closeds (Spec (.of A))) :
    IsDirectedAffineThickeningColimit (idealThickenings structureHom T)
      (completionAlong (Over.mk structureHom) T) :=
  sorry

/-- Inverse-limit projections on global sections of `idealThickenings` are
surjective, since each `A → A ⧸ J` is surjective. -/
theorem isSurjectiveLimitGlobalSections_idealThickenings {S : Scheme.{u}}
    {A : Type u} [CommRing A] (structureHom : Spec (.of A) ⟶ S)
    (T : Closeds (Spec (.of A))) :
    IsSurjectiveLimitGlobalSections (idealThickenings structureHom T) :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace

