/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.ClosedComparison
public import ReasLib.AlgebraicGeometry.Crystalline.ZariskiComparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.SmallToBig

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline.Base

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

/-- The small crystalline structure morphism to the small Zariski topos of the
base is the composite through the source and the canonical closed subscheme.
It does not require local nilpotence of the prime on the closed subscheme. -/
def structureMorphism : MorphismOfTopoiIn B.scheme.smallZariskiTopology
    (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
      B.source B.sourceToClosed B.prime_nilpotent) :=
  MorphismOfTopoiIn.comp
    (MorphismOfTopoiIn.comp
      (Zariski.SmallToBig.smallMorphism B.ideal.subschemeι)
      (Zariski.SmallToBig.smallMorphism B.sourceToClosed))
    (smallCrystallineToposMorphism B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
      B.source B.sourceToClosed B.prime_nilpotent)

/-- The inverse image of the small crystalline structure morphism is the
composite of the inverse images along its three defining arrows. -/
theorem structureMorphism_inverseImage :
    B.structureMorphism.inverseImage =
      (Zariski.SmallToBig.smallMorphism B.ideal.subschemeι).inverseImage ⋙
        (Zariski.SmallToBig.smallMorphism B.sourceToClosed).inverseImage ⋙
          (smallCrystallineToposMorphism B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
            B.source B.sourceToClosed B.prime_nilpotent).inverseImage := sorry

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

/-- The crystalline comparison with the canonical closed subscheme commutes,
up to natural isomorphism, with the morphisms to the small Zariski topoi. -/
theorem closedCrystallineMorphism_commSq :
    Nonempty
      ((smallCrystallineToposMorphism B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
          B.ideal.subscheme (𝟙 B.ideal.subscheme) h_p₀).inverseImage ⋙
          (B.closedCrystallineMorphism h_p₀).inverseImage ≅
        (Zariski.SmallToBig.smallMorphism B.sourceToClosed).inverseImage ⋙
          (smallCrystallineToposMorphism B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
            B.source B.sourceToClosed B.prime_nilpotent).inverseImage) := sorry

/-- When the prime is locally nilpotent on the canonical closed subscheme,
the crystalline structure morphism factors through its small crystalline topos. -/
theorem structureMorphism_closedFactorization :
    Nonempty
      (B.structureMorphism.inverseImage ≅
        (Zariski.SmallToBig.smallMorphism B.ideal.subschemeι).inverseImage ⋙
          (smallCrystallineToposMorphism B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
            B.ideal.subscheme (𝟙 B.ideal.subscheme) h_p₀).inverseImage ⋙
            (B.closedCrystallineMorphism h_p₀).inverseImage) := sorry

end AlgebraicGeometry.Scheme.Crystalline.Base
