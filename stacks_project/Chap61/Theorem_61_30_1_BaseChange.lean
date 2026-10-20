/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.Derived.BaseChange

/-! Completed derived base change on small pro-étale sites. -/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProEt AlgebraicGeometry.Scheme.ProetaleDerived RingedSite

universe u v

#check (AlgebraicGeometry.Scheme.ProEt.constantCoefficientUnderlyingIso :
  ∀ (Z : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    [HasWeakSheafify (topology Z) CommRingCat.{v}]
    [HasWeakSheafify (topology Z) RingCat.{v}]
    [HasWeakSheafify (topology Z) (Type v)]
    [(topology Z).HasSheafCompose (forget₂ CommRingCat.{v} RingCat.{v})]
    [(topology Z).HasSheafCompose (CategoryTheory.forget RingCat.{v})]
    [(topology Z).PreservesSheafification (forget₂ CommRingCat.{v} RingCat.{v})]
    [(topology Z).PreservesSheafification (CategoryTheory.forget RingCat.{v})],
    Hom.underlyingStructureSheaf
        (ofCommRingSheaf (topology Z) (constantCoefficientRing Z Λ)) ≅
      (constantSheaf (topology Z) (Type v)).obj Λ)
