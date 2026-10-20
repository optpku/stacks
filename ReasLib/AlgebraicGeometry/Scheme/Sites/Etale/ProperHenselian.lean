/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Henselian
public import ReasLib.AlgebraicGeometry.Scheme.EtaleCohomology.GabberH0

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a henselian pair `(A, I)` and a proper morphism over `Spec A`, restriction
to the special fibre induces a bijection on étale global sections of every
set-valued sheaf. -/
theorem etaleGlobalSectionsBijectiveOfProperHenselianPair
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] :
    let φ := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
    let i := pullback.fst f φ
    ∀ [HasWeakSheafify X.smallEtaleTopology (Type u)]
      [HasWeakSheafify (pullback f φ).smallEtaleTopology (Type u)]
      [∀ P : X.Etaleᵒᵖ ⥤ Type u, (smallEtalePullback i).op.HasLeftKanExtension P]
      (F : Sheaf X.smallEtaleTopology (Type u)),
      Function.Bijective (etaleGlobalSectionsPullback i F) := sorry

/-- For a proper scheme over a henselian local ring, restriction to the closed
fibre induces a bijection on étale global sections of every set-valued sheaf. -/
theorem etaleGlobalSectionsBijectiveOfProperHenselianLocal
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] :
    let φ := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))
    let i := pullback.fst f φ
    ∀ [HasWeakSheafify X.smallEtaleTopology (Type u)]
      [HasWeakSheafify (pullback f φ).smallEtaleTopology (Type u)]
      [∀ P : X.Etaleᵒᵖ ⥤ Type u, (smallEtalePullback i).op.HasLeftKanExtension P]
      (F : Sheaf X.smallEtaleTopology (Type u)),
      Function.Bijective (etaleGlobalSectionsPullback i F) := sorry

end AlgebraicGeometry.Scheme.Hom

end
