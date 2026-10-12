/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Conditions

/-!
# Zariski extension of presheaves from scheme subcategories

This leaf states the existence and uniqueness interface for extending a
presheaf on a sufficiently rich full subcategory of `Over S` to a Zariski
sheaf on all schemes over `S` that preserves directed affine limits.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry

namespace Scheme.Over.Extension

/-- A set-valued presheaf on a full subcategory of `Over S` satisfying the
affine-open, finite-presentation, Zariski-sheaf, and directed-affine-limit
conditions has a unique Zariski-sheaf extension to all schemes over `S` with
the same directed-affine-limit property. -/
theorem existsUniqueZariskiExtension
    {S : Scheme.{u}} (C : ObjectProperty (Over S))
    (F : C.FullSubcategoryᵒᵖ ⥤ Type (u + 1))
    (hC_open : ContainsAffineOpens C)
    (hC_fp : ContainsFinitelyPresentedAffines C)
    (hF_zariski : IsZariskiSheaf.{u, u + 1, u + 1} C F)
    (hF_limits : PreservesDirectedAffineLimits C F) :
    ∃ (F' : (Over S)ᵒᵖ ⥤ Type (u + 1)), ∃ (eF' : C.ι.op ⋙ F' ≅ F),
      ∃ (_ : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F'),
      ∃ (_ : Scheme.Over.PreservesDirectedAffineLimits S F'),
        ∀ (G : (Over S)ᵒᵖ ⥤ Type (u + 1)) (eG : C.ι.op ⋙ G ≅ F),
          Presheaf.IsSheaf (Scheme.zariskiTopology.over S) G →
          Scheme.Over.PreservesDirectedAffineLimits S G →
          ∃! α : F' ≅ G, Functor.isoWhiskerLeft C.ι.op α ≪≫ eG = eF' := sorry

end Scheme.Over.Extension

end AlgebraicGeometry
