module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper.SectionExtension
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Lemma 38.31.5: a section of a proper morphism over a quasi-compact open extends over the
inverse image of a larger quasi-compact open after an admissible blowup of the ambient scheme. -/
@[stacks 0CP1] #check
  (AlgebraicGeometry.exists_isAdmissibleBlowup_extending_section :
    ∀ {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
      (U W : S.Opens) (hUW : U ≤ W) [QuasiCompact U.ι] [QuasiCompact W.ι]
      (f : X ⟶ W.toScheme) [IsProper f]
      (s : U.toScheme ⟶ X) (hs : s ≫ f = S.homOfLE hUW),
      ∃ (S' : Scheme.{u}) (b : S' ⟶ S) (s' : (b ⁻¹ᵁ W).toScheme ⟶ X),
        IsAdmissibleBlowup U b ∧
          (b ∣_ U) ≫ s = S'.homOfLE (b.preimage_mono hUW) ≫ s' ∧
            s' ≫ f = b ∣_ W)

end AlgebraicGeometry
