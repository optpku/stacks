module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty

universe u v

/- Lemma 34.13.4: a sheaf on a localized big site satisfying directed-affine-limit
preservation has a sheaf extension for the same standard topology. -/
@[stacks 0EUX] #check
  (AlgebraicGeometry.StandardTopology.extension_isSheaf_of_isSheaf :
    ∀ {S : Scheme.{u}} (τ : StandardTopology) (C : ObjectProperty (Over S))
      (F : C.FullSubcategoryᵒᵖ ⥤ Type v) (F' : (Over S)ᵒᵖ ⥤ Type v)
      (hC_open : Scheme.Over.Extension.ContainsAffineOpens C)
      (hC_fp : Scheme.Over.Extension.ContainsFinitelyPresentedAffines C)
      (hF_tau : Presheaf.IsSheaf (C.ι.restrictedTopology (τ.overTopology S)) F)
      (hF_limits : Scheme.Over.Extension.PreservesDirectedAffineLimits C F)
      (eF' : C.ι.op ⋙ F' ≅ F)
      (hF'_zariski : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F')
      (hF'_limits : Scheme.Over.PreservesDirectedAffineLimits S F')
      (hF'_unique :
        ∀ (G : (Over S)ᵒᵖ ⥤ Type v) (eG : C.ι.op ⋙ G ≅ F),
          Presheaf.IsSheaf (Scheme.zariskiTopology.over S) G →
          Scheme.Over.PreservesDirectedAffineLimits S G →
          ∃! α : F' ≅ G, Functor.isoWhiskerLeft C.ι.op α ≪≫ eG = eF'),
      Presheaf.IsSheaf (τ.overTopology S) F')
