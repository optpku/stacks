/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Map

/-! The reusable construction is defined in the predeformation mapping module. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

/- The complete declaration is retained for proof-pending source consumers. -/
#check (AlgebraicGeometry.GroupoidsOver.Predeformation.map :
  ∀ {S : Scheme} [IsLocallyNoetherian S] {Λ k : Type} [CommRing Λ]
    [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    {kToS : Spec (CommRingCat.of k) ⟶ S} [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    {X Y : FiberedCategoryOver.Groupoids (Over S)} (F : X ⟶ Y)
    (x0 : X.p.Fiber (Over.mk kToS)),
    AlgebraicGeometry.GroupoidsOver.Predeformation.predeformation
        openImmersion h_factor X x0 ⥤ᵇ
      AlgebraicGeometry.GroupoidsOver.Predeformation.predeformation
        openImmersion h_factor Y
          (AlgebraicGeometry.GroupoidsOver.Predeformation.residueImage F x0))
