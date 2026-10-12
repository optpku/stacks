/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Affine

/-!
# McQuillan affine formal algebraic spaces

A McQuillan affine formal algebraic space admits a directed affine thickening
presentation with surjective inverse-limit projections on global sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- The inverse-limit projections on global sections of a diagram of affine
schemes are surjective: every global section of a stage extends to a
compatible family. -/
def IsSurjectiveLimitGlobalSections {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    {Λ : Type (max u v)} [Preorder Λ] (D : Λ ⥤ 𝒮.bigAffineSite S) : Prop :=
  ∀ (i : Λ) (x : Γ((𝒮.bigAffineToScheme S).obj (D.obj i), ⊤)),
    ∃ s : (j : Λ) → Γ((𝒮.bigAffineToScheme S).obj (D.obj j), ⊤),
      (∀ {j k : Λ} (f : j ⟶ k),
          ((𝒮.bigAffineToScheme S).map (D.map f)).appTop (s k) = s j) ∧
        s i = x

/-- Unfold surjectivity of inverse-limit projections on global sections as
existence of compatible families of sections. -/
theorem isSurjectiveLimitGlobalSections_iff {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} {Λ : Type (max u v)} [Preorder Λ]
    (D : Λ ⥤ 𝒮.bigAffineSite S) :
    IsSurjectiveLimitGlobalSections D ↔
      ∀ (i : Λ) (x : Γ((𝒮.bigAffineToScheme S).obj (D.obj i), ⊤)),
        ∃ s : (j : Λ) → Γ((𝒮.bigAffineToScheme S).obj (D.obj j), ⊤),
          (∀ {j k : Λ} (f : j ⟶ k),
              ((𝒮.bigAffineToScheme S).map (D.map f)).appTop (s k) = s j) ∧
            s i = x := sorry

/-- An affine formal algebraic space is McQuillan when some directed affine
thickening presentation has surjective inverse-limit projections on global
sections. -/
class IsMcQuillan {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsAffineFormalAlgebraicSpace X where
  /-- There is a directed affine thickening presentation whose inverse-limit
  projections on global sections are surjective. -/
  exists_surjective_limit_colimit :
    ∃ (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ 𝒮.bigAffineSite S),
        IsDirectedAffineThickeningColimit D X ∧ IsSurjectiveLimitGlobalSections D

namespace IsMcQuillan

/-- Exhibit a McQuillan affine formal algebraic space by a directed thickening
presentation with surjective inverse-limit projections on global sections. -/
theorem of {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAffineFormalAlgebraicSpace X]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ 𝒮.bigAffineSite S)
    (hcolim : IsDirectedAffineThickeningColimit D X)
    (hlim : IsSurjectiveLimitGlobalSections D) :
    IsMcQuillan X := sorry

/-- A McQuillan affine formal algebraic space admits a directed thickening
presentation with surjective inverse-limit projections on global sections. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsMcQuillan X] :
    ∃ (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ 𝒮.bigAffineSite S),
        IsDirectedAffineThickeningColimit D X ∧
          IsSurjectiveLimitGlobalSections D := sorry

/-- An affine formal algebraic space is McQuillan iff some directed thickening
presentation has surjective inverse-limit projections on global sections. -/
theorem iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsMcQuillan X ↔
      IsAffineFormalAlgebraicSpace X ∧
        ∃ (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
          (D : Λ ⥤ 𝒮.bigAffineSite S),
            IsDirectedAffineThickeningColimit D X ∧
              IsSurjectiveLimitGlobalSections D := sorry

/-- The sheafified representable of an affine object of `(Sch/S)_fppf` is
McQuillan, via the constant directed system. -/
instance instSheafifiedRepresentable {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (U : 𝒮.bigAffineSite S) :
    IsMcQuillan
      ((𝒮.bigTopology S).sheafifiedRepresentable
        ((𝒮.bigAffineInclusion S).obj U)) := sorry

end IsMcQuillan

end AlgebraicGeometry
