/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Base
public import ReasLib.AlgebraicGeometry.Crystalline.Site
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

/-- The source-forgetting functor from the big crystalline site of a prime-local
divided-power scheme with quasi-coherent ideal to its big Zariski site is cocontinuous. -/
instance crystallineForgetful_isCocontinuous {p : ℕ} [Fact p.Prime]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    [h_quasiCoherent : I.toModule.IsQuasicoherent]
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) :
    (crystallineForgetful S I γ h_compatible s X x₀ h_p).IsCocontinuous
      (crystallineZariskiTopology S I γ h_compatible X x₀)
      X.bigZariskiTopology := sorry

/-- A prime-local relative crystalline base determines a morphism from its big
crystalline topos to the big Zariski topos of its source, with sheaves valued in
`Type (u + 1)`. -/
noncomputable def Base.zariskiToposMorphism {p : ℕ} [Fact p.Prime] (B : Base.{u} p) :
    MorphismOfTopoiIn.{_, _, _, _, u + 1} B.source.bigZariskiTopology
      (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible
        B.source B.sourceToClosed) :=
  @Functor.morphismOfTopoiInOfCocontinuous _ _ _ _
    (crystallineForgetful B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
      B.source B.sourceToClosed B.prime_nilpotent)
    (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible
      B.source B.sourceToClosed) B.source.bigZariskiTopology
    (crystallineForgetful_isCocontinuous B.scheme B.ideal
      (h_quasiCoherent := B.quasiCoherent) B.dividedPowers B.compatible B.toSpec
      B.source B.sourceToClosed B.prime_nilpotent)
    (fun _ _ => inferInstance) inferInstance

end AlgebraicGeometry.Scheme.Crystalline
