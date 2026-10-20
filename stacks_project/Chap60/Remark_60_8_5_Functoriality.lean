/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.Remark_60_8_5_Functoriality_Functor
public import stacks_project.Chap60.Definition_60_8_4
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section Functoriality

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {S S' : Scheme.{u}} (I : S.IdealSheafData) (I' : S'.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (γ' : ∀ V : S'.affineOpens, DividedPowers (I'.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (h'_compatible :
  ∀ (V : S'.affineOpens) (f : Γ(S', V)),
    (γ' V).IsDPMorphism (γ' (S'.affineBasicOpen f))
      (S'.presheaf.map (homOfLE (S'.basicOpen_le f)).op).hom)
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (s' : S' ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable {X Y : Scheme.{u}} (x₀ : X ⟶ I.subscheme) (y₀ : Y ⟶ I'.subscheme)
variable (f : X ⟶ Y)
variable (g : DividedPowerSchemeHom I I' s s')
variable (h_comm : f ≫ y₀ = x₀ ≫ g.zeroFiberMap)
variable (h_dividedPowers_compatible :
  ∀ (V : S'.affineOpens) (W : S.affineOpens)
    (hVW : W.1 ≤ g.base ⁻¹ᵁ V.1),
    (γ' V).IsDPMorphism (γ W) (g.base.appLE V W hVW).hom)

/-- Remark 60.8.5 (Functoriality) (1): under the crystalline hypotheses, the
constructed functor of relative crystalline sites is continuous for the
canonical crystalline Zariski topologies. -/
@[stacks 07IC]
instance crystallineFunctor_isContinuous
    (pX : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (pY : ∀ U : Y.affineOpens, IsNilpotent (p : Γ(Y, U)))
    : (CrystallineFunctor.of f g h_comm pX pY
      h_dividedPowers_compatible).toRelativeFunctor.IsContinuous
      (Scheme.Crystalline.crystallineZariskiTopology S I γ h_compatible X x₀)
      (Scheme.Crystalline.crystallineZariskiTopology S' I' γ' h'_compatible Y y₀) := sorry

/-- Remark 60.8.5 (Functoriality) (2): under the crystalline hypotheses, the
constructed functor of relative crystalline sites is cocontinuous for the
canonical crystalline Zariski topologies. -/
@[stacks 07IC]
instance crystallineFunctor_isCocontinuous
    (pX : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (pY : ∀ U : Y.affineOpens, IsNilpotent (p : Γ(Y, U)))
    : (CrystallineFunctor.of f g h_comm pX pY
      h_dividedPowers_compatible).toRelativeFunctor.IsCocontinuous
      (Scheme.Crystalline.crystallineZariskiTopology S I γ h_compatible X x₀)
      (Scheme.Crystalline.crystallineZariskiTopology S' I' γ' h'_compatible Y y₀) := sorry

/-- Remark 60.8.5 (Functoriality) (3): the continuous and cocontinuous
crystalline-site functor induces `f_CRIS : (X/S)_CRIS ⟶ (Y/S')_CRIS`. -/
@[stacks 07IC]
noncomputable def crystallineToposHom
    (pX : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (pY : ∀ U : Y.affineOpens, IsNilpotent (p : Γ(Y, U)))
    [HasWeakSheafify
      (Scheme.Crystalline.crystallineZariskiTopology S' I' γ' h'_compatible Y y₀)
      (Type (u + 1))]
    [∀ P : (RelativeCRIS S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (Functor.op (CrystallineFunctor.of f g h_comm pX pY
        h_dividedPowers_compatible).toRelativeFunctor).HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((CrystallineFunctor.of f g h_comm pX pY
        h_dividedPowers_compatible).toRelativeFunctor.sheafPullback (Type (u + 1))
        (Scheme.Crystalline.crystallineZariskiTopology S I γ h_compatible X x₀)
        (Scheme.Crystalline.crystallineZariskiTopology S' I' γ' h'_compatible Y y₀))] :
    MorphismOfTopoiIn
      (Scheme.Crystalline.crystallineZariskiTopology S I γ h_compatible X x₀)
      (Scheme.Crystalline.crystallineZariskiTopology S' I' γ' h'_compatible Y y₀) :=
  (CrystallineFunctor.of f g h_comm pX pY
    h_dividedPowers_compatible).toRelativeFunctor.morphismOfTopoiInOfContinuous
    (Scheme.Crystalline.crystallineZariskiTopology S I γ h_compatible X x₀)
    (Scheme.Crystalline.crystallineZariskiTopology S' I' γ' h'_compatible Y y₀)

end Functoriality

end AlgebraicGeometry
