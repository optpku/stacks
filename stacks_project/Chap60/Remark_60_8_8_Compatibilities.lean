/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.StructureMorphism
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Crystalline

universe u

variable {p : ℕ} [Fact (Nat.Prime p)] (B B' : Base.{u} p)
variable (f : B.source ⟶ B'.source)
variable (g : DividedPowerSchemeHom B.ideal B'.ideal B.toSpec B'.toSpec)
variable (h_comm : f ≫ B'.sourceToClosed = B.sourceToClosed ≫ g.zeroFiberMap)
variable (h_dividedPowers_compatible :
  ∀ (V : B'.scheme.affineOpens) (W : B.scheme.affineOpens)
    (hVW : W.1 ≤ g.base ⁻¹ᵁ V.1),
    (B'.dividedPowers V).IsDPMorphism (B.dividedPowers W) (g.base.appLE V W hVW).hom)
variable [HasSheafify
  (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed) (Type (u + 1))]
variable [HasSheafify
  (crystallineZariskiTopology B'.scheme B'.ideal B'.dividedPowers B'.compatible
    B'.source B'.sourceToClosed) (Type (u + 1))]
variable [∀ P : (RelativeCRIS B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed)ᵒᵖ ⥤ Type (u + 1),
  (bigStructureFunctor B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
    B.source B.sourceToClosed B.prime_nilpotent).op.HasPointwiseRightKanExtension P]
variable [∀ P : (RelativeCRIS B'.scheme B'.ideal B'.dividedPowers B'.compatible
    B'.source B'.sourceToClosed)ᵒᵖ ⥤ Type (u + 1),
  (bigStructureFunctor B'.scheme B'.ideal B'.dividedPowers B'.compatible B'.toSpec
    B'.source B'.sourceToClosed B'.prime_nilpotent).op.HasPointwiseRightKanExtension P]

/- Remark 60.8.8 (Compatibilities)
The underlying morphisms of topoi commute up to a canonical natural isomorphism
of inverse images. The ringed enhancement fails for the source-object structure
functor: it would require maps from functions on U to functions on its thickening T,
including an impossible unital ring map 𝔽₃ → ℤ/9ℤ. -/
@[stacks 07MG] #check
  (AlgebraicGeometry.Scheme.Crystalline.crystallineToposHom_bigStructureMorphismIso
    B B' f g h_comm h_dividedPowers_compatible :
    (Scheme.Zariski.Big.morphismOfTopoi g.base).inverseImage ⋙
        (bigStructureMorphism B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
          B.source B.sourceToClosed B.prime_nilpotent).inverseImage ≅
      (bigStructureMorphism B'.scheme B'.ideal B'.dividedPowers B'.compatible B'.toSpec
          B'.source B'.sourceToClosed B'.prime_nilpotent).inverseImage ⋙
        (functorialToposHom B B' f g h_comm h_dividedPowers_compatible).inverseImage)
