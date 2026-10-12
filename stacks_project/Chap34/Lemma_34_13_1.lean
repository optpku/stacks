/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Zariski
import StacksCheckRecall

/-!
# Lemma 34.13.1

Compatibility facade for the reusable Zariski-extension interface on full
subcategories of schemes over a base.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty

universe u

/- Lemma 34.13.1: the affine-open, finite-presentation, Zariski-sheaf, and
directed-affine-limit conditions on a full subcategory of `Sch/S` yield a
unique Zariski-sheaf extension to all of `Sch/S`. -/
@[stacks 0EUW] #check
  (AlgebraicGeometry.Scheme.Over.Extension.existsUniqueZariskiExtension :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (C : ObjectProperty (Over S))
      (F : C.FullSubcategoryᵒᵖ ⥤ Type (u + 1)),
      AlgebraicGeometry.Scheme.Over.Extension.ContainsAffineOpens C →
      AlgebraicGeometry.Scheme.Over.Extension.ContainsFinitelyPresentedAffines C →
      AlgebraicGeometry.Scheme.Over.Extension.IsZariskiSheaf.{u, u + 1, u + 1} C F →
      AlgebraicGeometry.Scheme.Over.Extension.PreservesDirectedAffineLimits C F →
      ∃ (F' : (Over S)ᵒᵖ ⥤ Type (u + 1)), ∃ (eF' : C.ι.op ⋙ F' ≅ F),
        ∃ (_ : Presheaf.IsSheaf (AlgebraicGeometry.Scheme.zariskiTopology.over S) F'),
        ∃ (_ : AlgebraicGeometry.Scheme.Over.PreservesDirectedAffineLimits S F'),
          ∀ (G : (Over S)ᵒᵖ ⥤ Type (u + 1)) (eG : C.ι.op ⋙ G ≅ F),
            Presheaf.IsSheaf (AlgebraicGeometry.Scheme.zariskiTopology.over S) G →
            AlgebraicGeometry.Scheme.Over.PreservesDirectedAffineLimits S G →
            ∃! α : F' ≅ G, Functor.isoWhiskerLeft C.ι.op α ≪≫ eG = eF')
