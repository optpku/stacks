/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.TypeConditions
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Full

/-!
# Noetherian affine formal algebraic spaces

Equivalent characterizations in terms of closed immersions from schemes and
directed affine thickening presentations with Noetherian stages.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry.IsNoetherianAffine

/-- Every closed immersion `T ⟶ X` from a scheme `T` has `T` Noetherian. -/
def forallClosedImmersionIsNoetherian {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop :=
  ∀ (T : 𝒮.bigSite S) (t : (𝒮.bigTopology S).sheafifiedRepresentable T ⟶ X),
    (MorphismProperty.inverseImage (@IsClosedImmersion) (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor t →
      IsNoetherian ((𝒮.bigToScheme S).obj T)

/-- Unfold `forallClosedImmersionIsNoetherian` as: every relatively closed
immersion from a sheafified representable of a scheme over `S` has Noetherian
source. -/
theorem forallClosedImmersionIsNoetherian_iff {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    forallClosedImmersionIsNoetherian X ↔
      ∀ (T : 𝒮.bigSite S) (t : (𝒮.bigTopology S).sheafifiedRepresentable T ⟶ X),
        (MorphismProperty.inverseImage (@IsClosedImmersion) (𝒮.bigToScheme S)).relative
          (𝒮.bigTopology S).sheafifiedRepresentableFunctor t →
          IsNoetherian ((𝒮.bigToScheme S).obj T) :=
  Iff.rfl

/-- `X` admits some directed affine thickening presentation whose stages are Noetherian schemes. -/
def existsNoetherianThickeningColimit {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop :=
  ∃ (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
    (D : Λ ⥤ 𝒮.bigAffineSite S),
    IsDirectedAffineThickeningColimit D X ∧
      ∀ i, IsNoetherian ((𝒮.bigAffineToScheme S).obj (D.obj i))

/-- Unfold `existsNoetherianThickeningColimit` as existence of a directed set
`Λ : Type (max u v)` and a diagram of affine objects of `(Sch/S)_fppf` with
thickening transitions whose sheaf colimit is `X` and whose stages are
Noetherian. -/
theorem existsNoetherianThickeningColimit_iff {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    existsNoetherianThickeningColimit X ↔
      ∃ (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ 𝒮.bigAffineSite S),
        IsDirectedAffineThickeningColimit D X ∧
          ∀ i, IsNoetherian ((𝒮.bigAffineToScheme S).obj (D.obj i)) :=
  Iff.rfl

/-- For an affine formal algebraic space over a scheme, Noetherianity is
 equivalent to being adic* with every closed-immersed scheme Noetherian, to
 being adic* with some directed affine thickening presentation of Noetherian
 stages, and to being weakly adic with such a presentation. -/
@[stacks 0AKM]
theorem tfae {S : Scheme.{u}}
    [HasWeakSheafify (ChosenBigFppfSite.full.bigTopology S) (Type (u + 1))]
    [HasPullbacks (Sheaf (ChosenBigFppfSite.full.bigTopology S) (Type (u + 1)))]
    (X : Sheaf (ChosenBigFppfSite.full.bigTopology S) (Type (u + 1)))
    [IsAffineFormalAlgebraicSpace X] :
    List.TFAE [IsNoetherianAffine X,
      IsAdicStar X ∧ forallClosedImmersionIsNoetherian X,
      IsAdicStar X ∧ existsNoetherianThickeningColimit X,
      IsWeaklyAdicAffine X ∧ existsNoetherianThickeningColimit X] :=
  sorry

/-- A Noetherian affine formal algebraic space is exactly an adic* affine
formal algebraic space such that every closed immersion from a scheme is
Noetherian. -/
theorem iff_adicStar_forallClosedImmersion {S : Scheme.{u}}
    [HasWeakSheafify (ChosenBigFppfSite.full.bigTopology S) (Type (u + 1))]
    [HasPullbacks (Sheaf (ChosenBigFppfSite.full.bigTopology S) (Type (u + 1)))]
    (X : Sheaf (ChosenBigFppfSite.full.bigTopology S) (Type (u + 1)))
    [IsAffineFormalAlgebraicSpace X] :
    IsNoetherianAffine X ↔
      IsAdicStar X ∧ forallClosedImmersionIsNoetherian X :=
  (tfae X).out 0 1

/-- A Noetherian affine formal algebraic space is exactly an adic* affine
formal algebraic space admitting some directed affine
thickening presentation with Noetherian stages. -/
theorem iff_adicStar_existsNoetherianThickeningColimit
    {S : Scheme.{u}}
    [HasWeakSheafify (ChosenBigFppfSite.full.bigTopology S) (Type (u + 1))]
    [HasPullbacks (Sheaf (ChosenBigFppfSite.full.bigTopology S) (Type (u + 1)))]
    (X : Sheaf (ChosenBigFppfSite.full.bigTopology S) (Type (u + 1)))
    [IsAffineFormalAlgebraicSpace X] :
    IsNoetherianAffine X ↔
      IsAdicStar X ∧ existsNoetherianThickeningColimit X :=
  (tfae X).out 0 2

/-- A Noetherian affine formal algebraic space is exactly a weakly adic affine
formal algebraic space admitting some directed affine
thickening presentation with Noetherian stages. -/
theorem iff_weaklyAdic_existsNoetherianThickeningColimit
    {S : Scheme.{u}}
    [HasWeakSheafify (ChosenBigFppfSite.full.bigTopology S) (Type (u + 1))]
    [HasPullbacks (Sheaf (ChosenBigFppfSite.full.bigTopology S) (Type (u + 1)))]
    (X : Sheaf (ChosenBigFppfSite.full.bigTopology S) (Type (u + 1)))
    [IsAffineFormalAlgebraicSpace X] :
    IsNoetherianAffine X ↔
      IsWeaklyAdicAffine X ∧ existsNoetherianThickeningColimit X :=
  (tfae X).out 0 3

/-- A representable-by-algebraic-spaces, surjective, flat, locally finite type
morphism between affine formal algebraic spaces over a scheme preserves and
reflects Noetherianity. -/
@[stacks 0AKW]
theorem iff_of_surjective_flat
    {S : Scheme.{u}}
    [HasWeakSheafify (ChosenBigFppfSite.full.bigTopology S) (Type (u + 1))]
    [HasPullbacks (Sheaf (ChosenBigFppfSite.full.bigTopology S) (Type (u + 1)))]
    {X Y : Sheaf (ChosenBigFppfSite.full.bigTopology S) (Type (u + 1))}
    [IsAffineFormalAlgebraicSpace X] [IsAffineFormalAlgebraicSpace Y]
    {f : X ⟶ Y} (hf : ChosenBigFppfSite.representableByAlgebraicSpaces f)
    (h_surjective : (MorphismProperty.inverseImage (@Surjective : MorphismProperty Scheme)
        (ChosenBigFppfSite.full.bigToScheme S)).relative
      (ChosenBigFppfSite.full.bigTopology S).sheafifiedRepresentableFunctor f)
    (h_flat : (MorphismProperty.inverseImage (@Flat : MorphismProperty Scheme)
        (ChosenBigFppfSite.full.bigToScheme S)).relative
      (ChosenBigFppfSite.full.bigTopology S).sheafifiedRepresentableFunctor f)
    (h_locallyOfFiniteType : (MorphismProperty.inverseImage (@LocallyOfFiniteType)
        (ChosenBigFppfSite.full.bigToScheme S)).relative
      (ChosenBigFppfSite.full.bigTopology S).sheafifiedRepresentableFunctor f) :
    IsNoetherianAffine X ↔ IsNoetherianAffine Y :=
  sorry

end AlgebraicGeometry.IsNoetherianAffine
