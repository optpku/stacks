/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Crystalline.StructureMorphism.Small

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

variable {p : ℕ} [Fact p.Prime] (B : Base.{u} p)
variable [HasSheafify
  (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
    B.source B.sourceToClosed B.prime_nilpotent) (Type (u + 1))]
variable [HasSheafify B.source.smallZariskiTopology (Type (u + 1))]
variable [HasSheafify B.ideal.subscheme.smallZariskiTopology (Type (u + 1))]
variable [∀ P : (smallCrystallineSite B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed)ᵒᵖ ⥤ Type (u + 1),
  (forgetfulFunctor p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
    B.source B.sourceToClosed B.prime_nilpotent).op.HasPointwiseRightKanExtension P]

/- Remark 60.9.6 (Structure morphism).
The lower route through the source and the canonical closed subscheme defines
the crystalline structure morphism without local nilpotence on that subscheme. -/
@[stacks 07IM] #check (AlgebraicGeometry.Scheme.Crystalline.Base.structureMorphism B : MorphismOfTopoiIn B.scheme.smallZariskiTopology
    (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
      B.source B.sourceToClosed B.prime_nilpotent))

#check (AlgebraicGeometry.Scheme.Crystalline.Base.structureMorphism_inverseImage B :
    B.structureMorphism.inverseImage =
      (Zariski.SmallToBig.smallMorphism B.ideal.subschemeι).inverseImage ⋙
        (Zariski.SmallToBig.smallMorphism B.sourceToClosed).inverseImage ⋙
          (smallCrystallineToposMorphism B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
            B.source B.sourceToClosed B.prime_nilpotent).inverseImage)

variable (h_p₀ : ∀ U : B.ideal.subscheme.affineOpens, IsNilpotent (p : Γ(B.ideal.subscheme, U)))
variable [HasSheafify
  (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
    B.ideal.subscheme (𝟙 B.ideal.subscheme) h_p₀) (Type (u + 1))]
variable [HasWeakSheafify
  (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible
    B.ideal.subscheme (𝟙 B.ideal.subscheme)) (Type (u + 1))]
variable [∀ P : (smallCrystallineSite B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed)ᵒᵖ ⥤ Type (u + 1),
  (closedSourceFunctor B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed).op.HasPointwiseRightKanExtension P]
variable [∀ P : (smallCrystallineSite B.scheme B.ideal B.dividedPowers B.compatible
    B.ideal.subscheme (𝟙 B.ideal.subscheme))ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineProperty B.scheme B.ideal B.dividedPowers B.compatible
    B.ideal.subscheme (𝟙 B.ideal.subscheme)).ι.op.HasLeftKanExtension P]
variable [∀ P : (smallCrystallineSite B.scheme B.ideal B.dividedPowers B.compatible
    B.ideal.subscheme (𝟙 B.ideal.subscheme))ᵒᵖ ⥤ Type (u + 1),
  (forgetfulFunctor p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
    B.ideal.subscheme (𝟙 B.ideal.subscheme) h_p₀).op.HasPointwiseRightKanExtension P]

#check (AlgebraicGeometry.Scheme.Crystalline.Base.closedCrystallineMorphism B h_p₀ :
  MorphismOfTopoiIn
    (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
      B.ideal.subscheme (𝟙 B.ideal.subscheme) h_p₀)
    (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
      B.source B.sourceToClosed B.prime_nilpotent))

#check (AlgebraicGeometry.Scheme.Crystalline.Base.closedCrystallineMorphism_commSq B h_p₀ :
    Nonempty
      ((smallCrystallineToposMorphism B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
          B.ideal.subscheme (𝟙 B.ideal.subscheme) h_p₀).inverseImage ⋙
          (B.closedCrystallineMorphism h_p₀).inverseImage ≅
        (Zariski.SmallToBig.smallMorphism B.sourceToClosed).inverseImage ⋙
          (smallCrystallineToposMorphism B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
            B.source B.sourceToClosed B.prime_nilpotent).inverseImage))

#check (AlgebraicGeometry.Scheme.Crystalline.Base.structureMorphism_closedFactorization B h_p₀ :
    Nonempty
      (B.structureMorphism.inverseImage ≅
        (Zariski.SmallToBig.smallMorphism B.ideal.subschemeι).inverseImage ⋙
          (smallCrystallineToposMorphism B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
            B.ideal.subscheme (𝟙 B.ideal.subscheme) h_p₀).inverseImage ⋙
            (B.closedCrystallineMorphism h_p₀).inverseImage))

end AlgebraicGeometry.Scheme.Crystalline

