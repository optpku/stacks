/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Lifting
import StacksCheckRecall

/-!
# Lifting a quasi-isomorphism along a surjection of ring sheaves

On a site, a quasi-isomorphism `K₀ ⟶ F ⊗_O O₀` along a locally surjective
map of ring sheaves `O ⟶ O₀` lifts to a quasi-isomorphism `G ⟶ F` whose
extension of scalars factors through `K₀` in the homotopy category of
`O₀`-module complexes.
-/

@[expose] public section

open CategoryTheory SheafOfModules.RingedSite

universe u v w

/- Lemma 91.16.5: Let `C` be a site. Let `π : O ⟶ O₀` be a surjection of sheaves of rings.
Given a complex `F` of `O`-modules, a complex `K₀` of `O₀`-modules, and a quasi-isomorphism
`α : K₀ ⟶ (extendComplex π).obj F`, there exists a quasi-isomorphism `q : G ⟶ F` such that
`(extendComplex π).map q` factors through `α` in the homotopy category of complexes of
`O₀`-modules. -/
@[stacks 0DIX] #check (SheafOfModules.RingedSite.exists_quasiIso_homotopyFactor :
  ∀ {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {O O₀ : Sheaf J CommRingCat.{w}} (π : O ⟶ O₀)
    [Sheaf.IsLocallySurjective π]
    (F : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ)
    (K₀ : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O₀) ℤ)
    (α : K₀ ⟶ (extendComplex π).obj F) [QuasiIso α],
    ∃ (G : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ) (q : G ⟶ F),
      QuasiIso q ∧ ∃ (h : (extendComplex π).obj G ⟶ K₀),
        Nonempty (Homotopy ((extendComplex π).map q) (h ≫ α)))
