/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Crystalline.OpenRestriction

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline

universe u

noncomputable section

variable {p : ℕ} [Fact (Nat.Prime p)] (B B' : Base.{u} p)
variable (iX : B'.source ⟶ B.source) [IsOpenImmersion iX]
variable (g : DividedPowerSchemeHom B'.ideal B.ideal B'.toSpec B.toSpec)
variable [IsOpenImmersion g.base]
variable (h_comm : iX ≫ B.sourceToClosed = B'.sourceToClosed ≫ g.zeroFiberMap)
variable (h_dividedPowers :
  ∀ (V : B.scheme.affineOpens) (W : B'.scheme.affineOpens)
    (hVW : W.1 ≤ g.base ⁻¹ᵁ V.1),
    (B.dividedPowers V).IsDPMorphism (B'.dividedPowers W)
      (g.base.appLE V W hVW).hom)

variable [∀ P : (smallCrystallineSite B'.scheme B'.ideal B'.dividedPowers B'.compatible
    B'.source B'.sourceToClosed)ᵒᵖ ⥤ Type (u + 1),
  (openRestrictionFunctor iX B.ideal B'.ideal B.dividedPowers B'.dividedPowers
      B.compatible B'.compatible B.toSpec B'.toSpec B.sourceToClosed B'.sourceToClosed
      B.prime_nilpotent B'.prime_nilpotent g.base g.zeroFiberMap g.zeroFiber_comm
      g.base_over g.ideal_compatible h_comm h_dividedPowers).op.HasPointwiseRightKanExtension P]
variable [HasSheafify (smallCrystallineTopology p B'.scheme B'.ideal B'.dividedPowers B'.compatible
    B'.toSpec B'.source B'.sourceToClosed B'.prime_nilpotent) (Type (u + 1))]

#check (AlgebraicGeometry.Scheme.Crystalline.crystallineOpenSubschemeFullyFaithful
    B B' iX g h_comm h_dividedPowers : (openRestrictionFunctor iX B.ideal B'.ideal B.dividedPowers B'.dividedPowers
      B.compatible B'.compatible B.toSpec B'.toSpec B.sourceToClosed B'.sourceToClosed
      B.prime_nilpotent B'.prime_nilpotent g.base g.zeroFiberMap g.zeroFiber_comm
      g.base_over g.ideal_compatible h_comm h_dividedPowers).FullyFaithful)

variable [∀ P : (smallCrystallineSite B'.scheme B'.ideal B'.dividedPowers B'.compatible
    B'.source B'.sourceToClosed)ᵒᵖ ⥤ Type (u + 1),
  (forgetfulFunctor p B'.scheme B'.ideal B'.dividedPowers B'.compatible
      B'.toSpec B'.source B'.sourceToClosed B'.prime_nilpotent).op.HasPointwiseRightKanExtension P]
variable [∀ P : (smallCrystallineSite B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed)ᵒᵖ ⥤ Type (u + 1),
  (forgetfulFunctor p B.scheme B.ideal B.dividedPowers B.compatible
      B.toSpec B.source B.sourceToClosed B.prime_nilpotent).op.HasPointwiseRightKanExtension P]
variable [HasSheafify (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible
    B.toSpec B.source B.sourceToClosed B.prime_nilpotent) (Type (u + 1))]
variable [HasSheafify B'.source.smallZariskiTopology (Type (u + 1))]

#check (AlgebraicGeometry.Scheme.Crystalline.crystallineOpenSubschemeToposSquare
    B B' iX g h_comm h_dividedPowers : Nonempty
      ((Zariski.SmallToBig.smallMorphism iX).inverseImage ⋙ (smallCrystallineToposMorphism B'.scheme B'.ideal B'.dividedPowers
    B'.compatible B'.toSpec B'.source B'.sourceToClosed B'.prime_nilpotent).inverseImage ≅
        (smallCrystallineToposMorphism B.scheme B.ideal B.dividedPowers
    B.compatible B.toSpec B.source B.sourceToClosed B.prime_nilpotent).inverseImage ⋙ (openCrystallineToposMorphism B B' iX g h_comm h_dividedPowers).inverseImage))

variable [HasWeakSheafify B.source.smallZariskiTopology (Type (u + 1))]
variable [HasPullbacks (Sheaf B.source.smallZariskiTopology (Type (u + 1)))]
variable [HasBinaryProducts (Sheaf B.source.smallZariskiTopology (Type (u + 1)))]
variable [HasBinaryProducts (Sheaf (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible
    B.toSpec B.source B.sourceToClosed B.prime_nilpotent) (Type (u + 1)))]

variable (h_I'_restrict : B'.ideal = B.ideal.comap g.base)

/- Lemma 60.9.5. Compatible open subschemes induce a fully faithful crystalline functor
and the crystalline/Zariski square is a localization square of topoi. -/
@[stacks 07KL] #check
  (AlgebraicGeometry.Scheme.Crystalline.crystallineOpenSubschemeLocalization
    B B' iX g h_comm h_dividedPowers h_I'_restrict :
    let h := B.source.smallZariskiTopology.uliftSheafifiedRepresentable.{u + 1}
      (MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) iX
        (inferInstance : IsOpenImmersion iX))
    let u := (smallCrystallineToposMorphism B.scheme B.ideal B.dividedPowers
    B.compatible B.toSpec B.source B.sourceToClosed B.prime_nilpotent)
    let u' := (smallCrystallineToposMorphism B'.scheme B'.ideal B'.dividedPowers
    B'.compatible B'.toSpec B'.source B'.sourceToClosed B'.prime_nilpotent)
    let jZ := (Zariski.SmallToBig.smallMorphism iX)
    let jC := (openCrystallineToposMorphism B B' iX g h_comm h_dividedPowers)
    ∃ (eZ : Sheaf B'.source.smallZariskiTopology (Type (u + 1)) ≌ Over h)
      (eC : Sheaf (smallCrystallineTopology p B'.scheme B'.ideal B'.dividedPowers B'.compatible
    B'.toSpec B'.source B'.sourceToClosed B'.prime_nilpotent) (Type (u + 1)) ≌ Over (u.inverseImage.obj h)),
      Nonempty (jZ.inverseImage ⋙ eZ.functor ≅ Over.star h) ∧
      Nonempty (jC.inverseImage ⋙ eC.functor ≅ Over.star (u.inverseImage.obj h)) ∧
      Nonempty (u'.inverseImage ⋙ eC.functor ≅ eZ.functor ⋙ Over.post u.inverseImage))

end
