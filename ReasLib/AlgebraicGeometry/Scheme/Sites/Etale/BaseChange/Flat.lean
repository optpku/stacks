/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Set
public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Every small étale object over `X` admits an étale cover whose maps to `S`
factor through étale objects over `S` by quasi-compact morphisms with
geometrically connected fibres. -/
def HasConnectedFactorizationCover {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ U : X.Etale, ∃ 𝒰 : U.left.Cover.{u} (precoverage @Etale),
    ∀ i : 𝒰.I₀, ∃ (V : S.Etale) (φ : 𝒰.X i ⟶ V.left),
      QuasiCompact φ ∧ GeometricallyConnected φ ∧ φ ≫ V.hom = 𝒰.f i ≫ U.hom ≫ f

/-- A connected factorization cover supplies an étale cover of each small étale
object, with quasi-compact geometrically connected factorizations through
small étale objects of the base. -/
theorem HasConnectedFactorizationCover.exists_cover {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : HasConnectedFactorizationCover f) (U : X.Etale) :
    ∃ 𝒰 : U.left.Cover.{u} (precoverage @Etale),
      ∀ i : 𝒰.I₀, ∃ (V : S.Etale) (φ : 𝒰.X i ⟶ V.left),
        QuasiCompact φ ∧ GeometricallyConnected φ ∧ φ ≫ V.hom = 𝒰.f i ≫ U.hom ≫ f := sorry

namespace BaseChange

variable {X Y S T : Scheme.{u}}

/-- Flatness and étale-local quasi-compact geometrically connected factorizations
make the canonical set-valued comparison invertible for every cartesian square
and every small étale sheaf on the changed base. -/
theorem setMap_isIso_of_flat (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    [Flat f] (cart : IsPullback h e f g) (h_cover : HasConnectedFactorizationCover f)
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))) :
    IsIso (setMap f h e g cart F) := sorry

/-- Under flatness and connected factorization covers, every component of the
canonical set-valued base-change comparison is invertible. -/
theorem setMap_isIso_of_flat_app (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    [Flat f] (cart : IsPullback h e f g) (h_cover : HasConnectedFactorizationCover f)
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))) (U : X.Etaleᵒᵖ) :
    IsIso ((setMap f h e g cart F).hom.app U) := sorry

end BaseChange

end AlgebraicGeometry.Scheme.Etale

end
