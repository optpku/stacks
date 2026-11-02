/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineEtaleZariskiCover
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiLocalConditions

/-!
# Zero-dimensional algebraic spaces

Absolutely quasi-separated, locally-of-finite-type-over-a-field, and Noetherian
algebraic spaces of étale Krull dimension zero are separated schemes with affine
quasi-compact opens.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ZeroDimensional

private theorem isOpenImmersion_identity {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsOpenImmersion (𝟙 X) := by
  refine ⟨?_⟩
  change (MorphismProperty.over (@AlgebraicGeometry.IsOpenImmersion)).presheaf
    (𝟙 X.functorOfPoints)
  refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
  intro U V a fst snd h
  have : IsIso (yoneda.map snd) := h.isIso_snd_of_isIso
  have : IsIso snd := isIso_of_reflects_iso snd yoneda
  have : IsIso snd.left := inferInstanceAs (IsIso ((Over.forget S).map snd))
  change AlgebraicGeometry.IsOpenImmersion snd.left
  infer_instance

private theorem absolutelyQuasiSeparated_of_noetherianTerminal
    {S : Scheme.{u}} (X : AlgebraicSpace S) [IsNoetherian (extendBaseTerminal X)] :
    IsAbsolutelyQuasiSeparated X :=
  ⟨instIsQuasiSeparated_of_isAbsolutelyQuasiSeparated (extendBaseTerminal X)⟩

private theorem representable_of_affine_quasiCompact_opens
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : ∀ {U : AlgebraicSpace S} (j : U ⟶ X) [IsOpenImmersion j] [IsQuasiCompact U],
      IsAffine U) : X.functorOfPoints.IsRepresentable := by
  obtain ⟨𝒰⟩ := exists_affineEtaleZariskiCover X
  haveI : ∀ i, IsScheme (𝒰.cover.X i) := by
    intro i
    letI := 𝒰.cover.isOpenImmersion i
    letI := 𝒰.isAffine i
    letI : IsQuasiCompact (𝒰.cover.X i) :=
      ⟨𝒰.affine i, 𝒰.atlas i, 𝒰.etale i, 𝒰.locallySurjective i, inferInstance⟩
    obtain ⟨T, _, ⟨e⟩⟩ := (h (𝒰.cover.f i)).exists_affineScheme
    exact ⟨T, ⟨e⟩⟩
  haveI := IsScheme.of_zariskiCover 𝒰.cover
  obtain ⟨T, ⟨e⟩⟩ := IsScheme.exists_scheme (X := X)
  exact Functor.IsRepresentable.mk'
    { hom := e.inv, inv := e.hom, hom_inv_id := e.inv_hom_id, inv_hom_id := e.hom_inv_id }

/-- Every quasi-compact open of an absolutely quasi-separated algebraic space
of étale Krull dimension zero is affine. -/
theorem isAffine_of_isOpenImmersion
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X]
    (hdim : etaleKrullDim X = (0 : WithBot ℕ∞))
    {U : AlgebraicSpace S} (j : U ⟶ X) [IsOpenImmersion j] [IsQuasiCompact U] :
    IsAffine U := sorry

/-- An absolutely quasi-separated algebraic space of étale Krull dimension zero
has a representable functor of points. -/
theorem isRepresentable
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X]
    (hdim : etaleKrullDim X = (0 : WithBot ℕ∞)) :
    X.functorOfPoints.IsRepresentable := by
  apply representable_of_affine_quasiCompact_opens
  intro U j _ _
  exact isAffine_of_isOpenImmersion hdim j

/-- An absolutely quasi-separated algebraic space of étale Krull dimension zero
is separated over the terminal scheme. -/
theorem isSeparated
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X]
    (hdim : etaleKrullDim X = (0 : WithBot ℕ∞)) :
    IsSeparated (extendBaseTerminal X) := sorry

/-- A quasi-compact absolutely quasi-separated algebraic space of étale Krull
dimension zero is affine. -/
theorem isAffine
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact X] (hdim : etaleKrullDim X = (0 : WithBot ℕ∞)) :
    IsAffine X := by
  letI := isOpenImmersion_identity X
  exact isAffine_of_isOpenImmersion hdim (𝟙 X)

/-- Every quasi-compact open of an algebraic space of étale Krull dimension zero
that is locally of finite type over a field is affine. -/
theorem isAffine_of_isOpenImmersion_of_locallyOfFiniteType
    {S : Scheme.{u}} {X : AlgebraicSpace S} {k : Type u} [Field k]
    (f : extendBaseTerminal X ⟶ ofOver (Over.mk (terminal.from (Spec (.of k)))))
    [LocallyOfFiniteType f] (hdim : etaleKrullDim X = (0 : WithBot ℕ∞))
    {U : AlgebraicSpace S} (j : U ⟶ X) [IsOpenImmersion j] [IsQuasiCompact U] :
    IsAffine U := sorry

/-- An algebraic space of étale Krull dimension zero that is locally of finite
type over a field has a representable functor of points. -/
theorem isRepresentable_of_locallyOfFiniteType
    {S : Scheme.{u}} {X : AlgebraicSpace S} {k : Type u} [Field k]
    (f : extendBaseTerminal X ⟶ ofOver (Over.mk (terminal.from (Spec (.of k)))))
    [LocallyOfFiniteType f] (hdim : etaleKrullDim X = (0 : WithBot ℕ∞)) :
    X.functorOfPoints.IsRepresentable := by
  apply representable_of_affine_quasiCompact_opens
  intro U j _ _
  exact isAffine_of_isOpenImmersion_of_locallyOfFiniteType f hdim j

/-- An algebraic space of étale Krull dimension zero that is locally of finite
type over a field is separated over the terminal scheme. -/
theorem isSeparated_of_locallyOfFiniteType
    {S : Scheme.{u}} {X : AlgebraicSpace S} {k : Type u} [Field k]
    (f : extendBaseTerminal X ⟶ ofOver (Over.mk (terminal.from (Spec (.of k)))))
    [LocallyOfFiniteType f] (hdim : etaleKrullDim X = (0 : WithBot ℕ∞)) :
    IsSeparated (extendBaseTerminal X) := sorry

/-- A quasi-compact algebraic space of étale Krull dimension zero that is
locally of finite type over a field is affine. -/
theorem isAffine_of_locallyOfFiniteType
    {S : Scheme.{u}} {X : AlgebraicSpace S} {k : Type u} [Field k]
    (f : extendBaseTerminal X ⟶ ofOver (Over.mk (terminal.from (Spec (.of k)))))
    [LocallyOfFiniteType f] [IsQuasiCompact X]
    (hdim : etaleKrullDim X = (0 : WithBot ℕ∞)) : IsAffine X := by
  letI := isOpenImmersion_identity X
  exact isAffine_of_isOpenImmersion_of_locallyOfFiniteType f hdim (𝟙 X)

/-- Every quasi-compact open of an absolutely Noetherian algebraic space of
étale Krull dimension zero is affine. -/
theorem isAffine_of_isOpenImmersion_of_isNoetherian
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian (extendBaseTerminal X)]
    (hdim : etaleKrullDim X = (0 : WithBot ℕ∞))
    {U : AlgebraicSpace S} (j : U ⟶ X) [IsOpenImmersion j] [IsQuasiCompact U] :
    IsAffine U := by
  letI := absolutelyQuasiSeparated_of_noetherianTerminal X
  exact isAffine_of_isOpenImmersion hdim j

/-- An absolutely Noetherian algebraic space of étale Krull dimension zero has
a representable functor of points. -/
theorem isRepresentable_of_isNoetherian
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian (extendBaseTerminal X)]
    (hdim : etaleKrullDim X = (0 : WithBot ℕ∞)) :
    X.functorOfPoints.IsRepresentable := by
  letI := absolutelyQuasiSeparated_of_noetherianTerminal X
  exact isRepresentable hdim

/-- An absolutely Noetherian algebraic space of étale Krull dimension zero is
separated over the terminal scheme. -/
theorem isSeparated_of_isNoetherian
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian (extendBaseTerminal X)]
    (hdim : etaleKrullDim X = (0 : WithBot ℕ∞)) :
    IsSeparated (extendBaseTerminal X) := by
  letI := absolutelyQuasiSeparated_of_noetherianTerminal X
  exact isSeparated hdim

/-- An absolutely Noetherian algebraic space of étale Krull dimension zero is
affine. -/
theorem isAffine_of_isNoetherian
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian (extendBaseTerminal X)]
    (hdim : etaleKrullDim X = (0 : WithBot ℕ∞)) : IsAffine X := sorry

end AlgebraicGeometry.AlgebraicSpace.ZeroDimensional
