/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.FiniteGeneration
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Pushforward
import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Affine
import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Support

/-!
# Associated points under pushforward

This file excludes associated points outside the range of a quasi-compact and quasi-separated
morphism and compares associated and weakly associated points under affine pushforward from a
locally Noetherian scheme.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Pushforward

variable {X S : Scheme.{u}}

/-- A point outside the range of a quasi-compact and quasi-separated scheme morphism is not
associated to the pushforward of a quasicoherent module when the target stalk is Noetherian. -/
theorem not_mem_associatedPoints_of_not_mem_range
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (s : S) [IsNoetherianRing (S.presheaf.stalk s)]
    (hs : s ∉ Set.range f.base) :
    s ∉ associatedPoints ((Scheme.Modules.pushforward f).obj ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules.Pushforward

namespace AlgebraicGeometry.Scheme.Modules.AffinePushforward

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f]
variable (ℱ : X.Modules) [ℱ.IsQuasicoherent] [IsLocallyNoetherian X]

/-- Under an affine morphism from a locally Noetherian scheme, the image of the associated points
of a quasicoherent module is the set of associated points of its pushforward. -/
theorem image_associatedPoints_eq_associatedPoints :
    f.base '' ℱ.associatedPoints =
      ((Scheme.Modules.pushforward f).obj ℱ).associatedPoints := sorry

/-- For an affine pushforward from a locally Noetherian scheme, the associated and weakly
associated points of a quasicoherent module coincide. -/
theorem associatedPoints_eq_weakAss :
    ((Scheme.Modules.pushforward f).obj ℱ).associatedPoints =
      ((Scheme.Modules.pushforward f).obj ℱ).weakAss := sorry

/-- Under an affine morphism from a locally Noetherian scheme, the weakly associated points of a
quasicoherent module's pushforward are the images of its weakly associated points. -/
theorem weakAss_eq_image_weakAss :
    ((Scheme.Modules.pushforward f).obj ℱ).weakAss = f.base '' ℱ.weakAss := by
  rw [← associatedPoints_eq_weakAss f ℱ]
  rw [← image_associatedPoints_eq_associatedPoints f ℱ]
  rw [associatedPoints_eq_weakAss_of_isLocallyNoetherian ℱ]

/-- The image of the associated points, the associated and weakly associated points of an affine
pushforward, and the image of the weakly associated points form an equality chain when the source
scheme is locally Noetherian. -/
theorem associatedPoints_weakAss_chain :
    List.IsChain (· = ·)
      [f.base '' ℱ.associatedPoints,
        ((Scheme.Modules.pushforward f).obj ℱ).associatedPoints,
        ((Scheme.Modules.pushforward f).obj ℱ).weakAss,
        f.base '' ℱ.weakAss] := by
  simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
  exact
    ⟨image_associatedPoints_eq_associatedPoints f ℱ,
      associatedPoints_eq_weakAss f ℱ,
      weakAss_eq_image_weakAss f ℱ⟩

/-- A point is associated to an affine pushforward from a locally Noetherian scheme exactly when
it is the image of an associated point of the original quasicoherent module. -/
theorem mem_associatedPoints_iff_exists (s : S) :
    s ∈ ((Scheme.Modules.pushforward f).obj ℱ).associatedPoints ↔
      ∃ x : X, x ∈ ℱ.associatedPoints ∧ f.base x = s := by
  rw [← image_associatedPoints_eq_associatedPoints f ℱ]
  simpa [Set.mem_image]

/-- A point is associated to an affine pushforward from a locally Noetherian scheme exactly when
it is weakly associated to that pushforward. -/
theorem mem_associatedPoints_iff_mem_weakAss (s : S) :
    s ∈ ((Scheme.Modules.pushforward f).obj ℱ).associatedPoints ↔
      s ∈ ((Scheme.Modules.pushforward f).obj ℱ).weakAss := by
  rw [associatedPoints_eq_weakAss f ℱ]

/-- A point is weakly associated to an affine pushforward from a locally Noetherian scheme exactly
when it is the image of a weakly associated point of the original quasicoherent module. -/
theorem mem_weakAss_iff_exists (s : S) :
    s ∈ ((Scheme.Modules.pushforward f).obj ℱ).weakAss ↔
      ∃ x : X, x ∈ ℱ.weakAss ∧ f.base x = s := by
  rw [weakAss_eq_image_weakAss f ℱ]
  simpa [Set.mem_image]

end AlgebraicGeometry.Scheme.Modules.AffinePushforward
