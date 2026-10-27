/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.ZariskiComparison
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline

universe u

section

variable {p : ℕ} [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))

/- Remark 60.9.4 (Comparison with Zariski site) (1): the small crystalline
   forgetful functor is continuous. -/
@[stacks 07IL] #check
  (AlgebraicGeometry.Scheme.Crystalline.forgetfulFunctor_isContinuous
      S I γ h_compatible s X x₀ h_p :
    (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).IsContinuous
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      X.smallZariskiTopology)

/- Remark 60.9.4 (Comparison with Zariski site) (2): the small crystalline
   forgetful functor is cocontinuous. -/
@[stacks 07IL] #check
  (AlgebraicGeometry.Scheme.Crystalline.forgetfulFunctor_isCocontinuous
      S I γ h_compatible s X x₀ h_p :
    (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).IsCocontinuous
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      X.smallZariskiTopology)

/- Remark 60.9.4 (Comparison with Zariski site) (3): the forgetful functor
   preserves products and fibre products via finite nonempty limits. -/
@[stacks 07IL] #check
  (AlgebraicGeometry.Scheme.Crystalline.forgetfulFunctor_preservesFiniteNonemptyLimits
      S I γ h_compatible s X x₀ h_p :
    PreservesFiniteNonemptyLimits (forgetfulFunctor p S I γ h_compatible s X x₀ h_p))

variable [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (Type (u + 1))]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P]

/- Remark 60.9.4 (Comparison with Zariski site) (4): these properties induce
   the canonical morphism from the small crystalline topos to the small Zariski topos. -/
@[stacks 07IL] #check
  (AlgebraicGeometry.Scheme.Crystalline.smallCrystallineToposMorphism
      S I γ h_compatible s X x₀ h_p :
    MorphismOfTopoiIn X.smallZariskiTopology
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p))

end
