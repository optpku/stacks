module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf
import StacksCheckRecall

/-!
# Lemma 34.13.3

Source bridge to the standard-cover sheaf test for extensions of functors on
schemes over a base.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.ObjectProperty

universe u v

/- Lemma 34.13.3: a Zariski extension satisfying descent for finite standard
covers of suitably presented affine schemes is a sheaf for the selected
standard topology. -/
@[stacks 0GDW] #check
  (AlgebraicGeometry.StandardTopology.Affine.extension_isSheaf :
    ∀ {S : Scheme.{u}} (C : ObjectProperty (Over S))
      (F : C.FullSubcategoryᵒᵖ ⥤ Type v) (F' : (Over S)ᵒᵖ ⥤ Type v)
      (hC_open : Scheme.Over.Extension.ContainsAffineOpens C)
      (hC_fp : Scheme.Over.Extension.ContainsFinitelyPresentedAffines C)
      (hF_zariski : Scheme.Over.Extension.IsZariskiSheaf C F)
      (hF_limits : Scheme.Over.Extension.PreservesDirectedAffineLimits C F)
      (eF' : C.ι.op ⋙ F' ≅ F)
      (hF'_zariski : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F')
      (hF'_limits : Scheme.Over.PreservesDirectedAffineLimits S F')
      (hF'_unique :
        ∀ (G : (Over S)ᵒᵖ ⥤ Type v) (eG : C.ι.op ⋙ G ≅ F),
          Presheaf.IsSheaf (Scheme.zariskiTopology.over S) G →
          Scheme.Over.PreservesDirectedAffineLimits S G →
          ∃! α : F' ≅ G, Functor.isoWhiskerLeft C.ι.op α ≪≫ eG = eF')
      (τ : AlgebraicGeometry.StandardTopology)
      (hF_standard : AlgebraicGeometry.StandardTopology.Affine.IsSheaf C τ F),
      Presheaf.IsSheaf (τ.overTopology S) F')
