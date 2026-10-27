/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.MayerVietoris
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry TopologicalSpace
open RingedSite RingedSite.Hom
open AlgebraicGeometry.Scheme.Crystalline

noncomputable section

universe u

/- Remark 60.24.2 (Mayer-Vietoris)
For a compatible morphism of prime-local divided-power bases and source schemes,
a cover of the source by two opens gives a distinguished triangle of crystalline
derived direct images. The coefficients on each open and their intersection are
the restrictions of the original module sheaf. The three vertices are the global
direct image, the biproduct of the two open direct images, and the intersection
direct image; the last arrow maps to the positive-one shift of the first vertex.
-/
@[stacks 07ML] #check
  (AlgebraicGeometry.Scheme.Crystalline.crystallinePushforward_mayerVietoris_triangle :
    ∀ {p : ℕ} [Fact p.Prime] (B B' : Base.{u} p)
    (g : DividedPowerScheme.Hom B.dividedPowerScheme B'.dividedPowerScheme)
    (hbase : g.base ≫ B'.toSpec = B.toSpec) (f : B.source ⟶ B'.source)
    (hf : f ≫ B'.sourceToClosed = B.sourceToClosed ≫ g.zeroFiberMap)
    (U V : Opens B.source) (hUV : U ⊔ V = ⊤)
    (F : RingedSite.ModuleCat.{u + 1} B.ringedSite),
    let fC := Ringed.morphism B B' g hbase f hf
    let A := (Ringed.derivedPushforward fC).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)
    let P := fun W : Opens B.source ↦
      (Ringed.derivedPushforward
        (RingedSite.ToposHom.comp
          (X := (B.restrictOpen W).ringedSite) (Y := B.ringedSite) (Z := B'.ringedSite)
          (Ringed.openInclusion B W) fC)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((Ringed.openInclusion B W).modulePullback.obj F))
    ∃ α : A ⟶ P U ⊞ P V,
      ∃ β : P U ⊞ P V ⟶ P (U ⊓ V),
        ∃ δ : P (U ⊓ V) ⟶
          (shiftFunctor (ModuleDerived.{u + 1} B'.ringedSite) (1 : ℤ)).obj A,
          Triangle.mk α β δ ∈ distTriang (ModuleDerived.{u + 1} B'.ringedSite))
