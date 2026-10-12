/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived.EssentialImage

import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.PerfectDerived

/- Lemma 57.12.4 -/
@[stacks 0GX0] #check (AlgebraicGeometry.SchemeOverField.PerfectDerived.essImage_le_of_iso_on_zeroDimensional_coherent :
    ∀ {k : Type u} [inst : Field k] (X Y : SchemeOverField k)
      [hX : IsProper X.hom] [hY : IsProper Y.hom] [hRegular : Scheme.Regular X.left]
      (F G : PerfectDerived X ⥤ PerfectDerived Y)
      [hF_linear : F.Linear k] [hG_linear : G.Linear k]
      (hF_exact : F.HasTriangulatedStructure) (hG_exact : G.HasTriangulatedStructure)
      [hF_full : F.Full] [hF_faithful : F.Faithful]
      (h_agree : ∀ (ℱ : X.left.Modules) [hCoherent : SheafOfModules.IsCoherent ℱ],
        topologicalKrullDim (moduleSupport ℱ) = 0 →
          Nonempty (F.obj (ofCoherentModule X ℱ) ≅ G.obj (ofCoherentModule X ℱ))),
      G.essImage ≤ F.essImage)

end AlgebraicGeometry.SchemeOverField.PerfectDerived

end
