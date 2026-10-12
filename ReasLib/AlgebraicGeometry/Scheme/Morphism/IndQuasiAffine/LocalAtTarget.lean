/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.IndQuasiAffine.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Operations
public import Mathlib.Data.List.TFAE

/-!
# Target Locality of Ind-Quasi-Affine Scheme Morphisms

This file characterizes ind-quasi-affine scheme morphisms using compact opens
and records that ind-quasi-affineness is Zariski local on the target.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- For a scheme morphism, ind-quasi-affineness is equivalent to the
compact-open quasi-affineness criterion over every affine target open, over
some quasi-compact and quasi-separated open cover, or over every
quasi-compact and quasi-separated target open. -/
theorem indQuasiAffineHom_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
    List.TFAE
      [ IndQuasiAffineHom f
      , ∀ V : Y.affineOpens, (f ∣_ V).IsQuasiAffineOnCompactOpens
      , ∃ (J : Type u) (V : J → Y.Opens), iSup V = ⊤ ∧
          ∀ j : J, IsCompact (V j : Set Y) ∧ QuasiSeparatedSpace (V j).toScheme ∧
            (f ∣_ (V j)).IsQuasiAffineOnCompactOpens
      , ∀ V : Y.Opens, IsCompact (V : Set Y) → QuasiSeparatedSpace V.toScheme →
          (f ∣_ V).IsQuasiAffineOnCompactOpens
      ] := sorry

namespace IndQuasiAffineHom

/-- Ind-quasi-affineness of scheme morphisms is Zariski local on the target. -/
@[instance]
theorem isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (@IndQuasiAffineHom : MorphismProperty Scheme.{u}) := sorry

end IndQuasiAffineHom

end AlgebraicGeometry
