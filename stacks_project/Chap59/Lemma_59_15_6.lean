/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fpqc.Sheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/- Lemma 59.15.6: for a presheaf `F` on schemes over `S`, fpqc sheafness is
equivalent to Zariski sheafness together with the singleton sheaf axiom for
every faithfully flat morphism between affine schemes over `S`; the singleton
condition is the associated equalizer diagram. -/
@[stacks 03O1] #check
  (AlgebraicGeometry.isSheaf_fpqcTopology_over_iff_zariski_and_affineFaithfullyFlat :
    ∀ (S : Scheme.{u}) (F : (CategoryTheory.Over S)ᵒᵖ ⥤ Type v),
      Presheaf.IsSheaf (Scheme.fpqcTopology.over S) F ↔
        Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F ∧
          (∀ {U V : CategoryTheory.Over S} (f : V ⟶ U)
            [IsAffine U.left] [IsAffine V.left] [Flat f.left] [Surjective f.left],
            Presieve.IsSheafFor F (Presieve.singleton f)))

end AlgebraicGeometry
