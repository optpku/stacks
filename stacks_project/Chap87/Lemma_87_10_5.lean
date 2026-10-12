/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap87.Lemma_87_10_3_Types

/-!
# Lemma 87.10.5

Equivalent characterizations of Noetherian affine formal algebraic spaces:
adic* with Noetherian scheme closed immersions, or adic*/weakly adic with some
Definition 87.9.1 directed affine thickening presentation of Noetherian stages.
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
  sorry

/-- `X` admits some directed affine thickening presentation as in
Definition 87.9.1 whose stages are Noetherian schemes. -/
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
  sorry

/-- Lemma 87.10.5: Let `S` be a scheme. Let `X` be an affine formal algebraic
space. The following are equivalent: `X` is Noetherian; `X` is adic* and for
every closed immersion `T ⟶ X` with `T` a scheme, `T` is Noetherian; `X` is
adic* and for some choice of `X = colim X_λ` as in Definition 87.9.1 the
schemes `X_λ` are Noetherian; and `X` is weakly adic and for some choice
`X = colim X_λ` as in Definition 87.9.1 the schemes `X_λ` are Noetherian. -/
@[stacks 0AKM]
theorem tfae {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    List.TFAE [IsNoetherianAffine X,
      IsAdicStar X ∧ forallClosedImmersionIsNoetherian X,
      IsAdicStar X ∧ existsNoetherianThickeningColimit X,
      IsWeaklyAdicAffine X ∧ existsNoetherianThickeningColimit X] :=
  sorry

/-- A Noetherian affine formal algebraic space is exactly an adic* affine
formal algebraic space such that every closed immersion from a scheme is
Noetherian. -/
theorem iff_adicStar_forallClosedImmersion {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    IsNoetherianAffine X ↔
      IsAdicStar X ∧ forallClosedImmersionIsNoetherian X :=
  sorry

/-- A Noetherian affine formal algebraic space is exactly an adic* affine
formal algebraic space admitting some Definition 87.9.1 directed affine
thickening presentation with Noetherian stages. -/
theorem iff_adicStar_existsNoetherianThickeningColimit
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    IsNoetherianAffine X ↔
      IsAdicStar X ∧ existsNoetherianThickeningColimit X :=
  sorry

/-- A Noetherian affine formal algebraic space is exactly a weakly adic affine
formal algebraic space admitting some Definition 87.9.1 directed affine
thickening presentation with Noetherian stages. -/
theorem iff_weaklyAdic_existsNoetherianThickeningColimit
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    IsNoetherianAffine X ↔
      IsWeaklyAdicAffine X ∧ existsNoetherianThickeningColimit X :=
  sorry

end AlgebraicGeometry.IsNoetherianAffine
