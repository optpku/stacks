/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.Topology.Adic.Complete
public import stacks_project.Chap87.Lemma_87_37_4_Completion
public import stacks_project.Chap87.Lemma_87_37_6_Affine
public import stacks_project.Chap87.Lemma_87_37_6_CountablyIndexed

/-!
# Types of the recompletion of an affine formal algebraic space

The completion of an affine formal algebraic space along a closed subset of
its reduction remains affine. McQuillan and Noetherian pass unconditionally;
countably indexed and adic* pass when the complement of `T` in the reduction
is quasi-compact.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace (Points)
open AlgebraicGeometry.FormalAlgebraicSpace
open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

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

/-- The affine stage `Spec(A ⧸ I^(n+1))` over `S` along `structureHom`. -/
def specQuotientPowerOver {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) : Over S :=
  Over.mk
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) ≫ structureHom)

/-- The underlying scheme of `specQuotientPowerOver structureHom I n` is
`Spec(A ⧸ I^(n+1))`. -/
theorem specQuotientPowerOver_left {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    (specQuotientPowerOver structureHom I n).left =
      Spec (.of (A ⧸ I ^ (n + 1))) :=
  sorry

/-- The structure morphism of `specQuotientPowerOver structureHom I n` is
`Spec` of the quotient map composed with `structureHom`. -/
theorem specQuotientPowerOver_hom {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    (specQuotientPowerOver structureHom I n).hom =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) ≫
        structureHom :=
  sorry

/-- Lemma 87.37.6 (1): Let `S` be a scheme. Let `X` be an affine formal
algebraic space over `S`. Let `T ⊆ Points (reduction X)` be a closed subset.
Then the completion `completionAlong X T` is an affine formal algebraic
space. -/
@[stacks 0GVV]
instance instIsAffine_completionAlong {S : Scheme.{u}}
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X] [Reduction X]
    [AffineFormalAlgebraicSpace.IsAffine X]
    (T : Closeds (Points (reduction X))) :
    AffineFormalAlgebraicSpace.IsAffine (completionAlong X T) :=
  sorry

/-- Lemma 87.37.6 (2): In the situation of Lemma 87.37.6 (1), if `X` is
McQuillan, then `completionAlong X T` is McQuillan. -/
@[stacks 0GVV]
theorem isMcQuillanAffine_completionAlong {S : Scheme.{u}}
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X] [Reduction X]
    [AffineFormalAlgebraicSpace.IsAffine X]
    (hX : ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ Over S),
      IsDirectedAffineThickeningColimit D X ∧
        IsSurjectiveLimitGlobalSections D)
    (T : Closeds (Points (reduction X))) :
    AffineFormalAlgebraicSpace.IsAffine (completionAlong X T) ∧
      ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ Over S),
        IsDirectedAffineThickeningColimit D (completionAlong X T) ∧
          IsSurjectiveLimitGlobalSections D :=
  sorry

/-- Lemma 87.37.6 (3): In the situation of Lemma 87.37.6 (1), if
`|X_red| \ T` is quasi-compact and `X` is countably indexed, then
`completionAlong X T` is countably indexed. -/
@[stacks 0GVV]
theorem isCountablyIndexedAffine_completionAlong {S : Scheme.{u}}
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsCountablyIndexedAffine X] [Reduction X]
    (T : Closeds (Points (reduction X)))
    (hT : IsCompact (T.compl : Set (Points (reduction X)))) :
    IsCountablyIndexedAffine (completionAlong X T) :=
  sorry

/-- Lemma 87.37.6 (4): In the situation of Lemma 87.37.6 (1), if
`|X_red| \ T` is quasi-compact and `X` is adic*, then
`completionAlong X T` is adic*. -/
@[stacks 0GVV]
theorem isAdicStarAffine_completionAlong {S : Scheme.{u}}
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X] [Reduction X]
    [AffineFormalAlgebraicSpace.IsAffine X]
    (hX : ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : TopologicalRing.IsAdicRing A) (I : Ideal A) (_ : I.FG)
        (_ : TopologicalRing.Ideal.IsIdealOfDefinition I)
        (structureHom : Spec (.of A) ⟶ S) (D : ℕ ⥤ Over S),
          (∀ n : ℕ,
              Nonempty (D.obj n ≅ specQuotientPowerOver structureHom I n)) ∧
            IsDirectedAffineThickeningColimit D X)
    (T : Closeds (Points (reduction X)))
    (hT : IsCompact (T.compl : Set (Points (reduction X)))) :
    AffineFormalAlgebraicSpace.IsAffine (completionAlong X T) ∧
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : TopologicalRing.IsAdicRing A) (I : Ideal A) (_ : I.FG)
        (_ : TopologicalRing.Ideal.IsIdealOfDefinition I)
        (structureHom : Spec (.of A) ⟶ S) (D : ℕ ⥤ Over S),
          (∀ n : ℕ,
              Nonempty (D.obj n ≅ specQuotientPowerOver structureHom I n)) ∧
            IsDirectedAffineThickeningColimit D (completionAlong X T) :=
  sorry

/-- Lemma 87.37.6 (5): In the situation of Lemma 87.37.6 (1), if `X` is
Noetherian, then `completionAlong X T` is Noetherian. -/
@[stacks 0GVV]
theorem isNoetherianAffine_completionAlong {S : Scheme.{u}}
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X] [Reduction X]
    [AffineFormalAlgebraicSpace.IsAffine X]
    (hX : ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : TopologicalRing.IsAdicRing A) (_ : IsNoetherianRing A)
        (I : Ideal A) (_ : TopologicalRing.Ideal.IsIdealOfDefinition I)
        (structureHom : Spec (.of A) ⟶ S) (D : ℕ ⥤ Over S),
          (∀ n : ℕ,
              Nonempty (D.obj n ≅ specQuotientPowerOver structureHom I n)) ∧
            IsDirectedAffineThickeningColimit D X)
    (T : Closeds (Points (reduction X))) :
    AffineFormalAlgebraicSpace.IsAffine (completionAlong X T) ∧
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : TopologicalRing.IsAdicRing A) (_ : IsNoetherianRing A)
        (I : Ideal A) (_ : TopologicalRing.Ideal.IsIdealOfDefinition I)
        (structureHom : Spec (.of A) ⟶ S) (D : ℕ ⥤ Over S),
          (∀ n : ℕ,
              Nonempty (D.obj n ≅ specQuotientPowerOver structureHom I n)) ∧
            IsDirectedAffineThickeningColimit D (completionAlong X T) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
