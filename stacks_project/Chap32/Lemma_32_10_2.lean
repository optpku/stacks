/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Limit.FinitePresentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 32.10.2 (1): finitely presented modules on the limit descend to a stage. -/
@[stacks 01ZR] #check
  (AlgebraicGeometry.Scheme.Modules.Limit.FinitePresentation.exists_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ j, CompactSpace (D.obj j).carrier]
      [∀ j, QuasiSeparatedSpace (D.obj j).carrier]
      [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
      (ℱ : c.pt.Modules) [ℱ.IsFinitePresentation],
      ∃ (i : I) (ℱi : (D.obj i).Modules),
        ℱi.IsFinitePresentation ∧
          Nonempty ((Scheme.Modules.pullback (c.π.app i)).obj ℱi ≅ ℱ))

/- Lemma 32.10.2 (2): morphisms between pullbacks of finitely presented stage modules descend
after passing to a later stage. -/
@[stacks 01ZR] #check
  (AlgebraicGeometry.Scheme.Modules.Limit.FinitePresentation.exists_hom_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ j, CompactSpace (D.obj j).carrier]
      [∀ j, QuasiSeparatedSpace (D.obj j).carrier]
      [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
      (i : I) (ℱi 𝒢i : (D.obj i).Modules)
      [ℱi.IsFinitePresentation] [𝒢i.IsFinitePresentation]
      (φ : (Scheme.Modules.pullback (c.π.app i)).obj ℱi ⟶
        (Scheme.Modules.pullback (c.π.app i)).obj 𝒢i),
      ∃ (i' : I) (hii' : i ≤ i')
        (hcomp : c.π.app i' ≫ D.map (homOfLE hii') = c.π.app i)
        (φi' : (Scheme.Modules.pullback (D.map (homOfLE hii'))).obj ℱi ⟶
          (Scheme.Modules.pullback (D.map (homOfLE hii'))).obj 𝒢i),
        (Scheme.Modules.pullbackComp (c.π.app i') (D.map (homOfLE hii'))).inv.app ℱi ≫
            (Scheme.Modules.pullback (c.π.app i')).map φi' ≫
          (Scheme.Modules.pullbackComp (c.π.app i') (D.map (homOfLE hii'))).hom.app 𝒢i =
          (Scheme.Modules.pullbackCongr hcomp).hom.app ℱi ≫ φ ≫
            (Scheme.Modules.pullbackCongr hcomp).inv.app 𝒢i)

/- Lemma 32.10.2 (3): equality of morphisms detected on the limit is detected at a later
stage. -/
@[stacks 01ZR] #check
  (AlgebraicGeometry.Scheme.Modules.Limit.FinitePresentation.exists_eq_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ j, CompactSpace (D.obj j).carrier]
      [∀ j, QuasiSeparatedSpace (D.obj j).carrier]
      [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
      (i : I) (ℱi 𝒢i : (D.obj i).Modules)
      [ℱi.IsFinitePresentation] [𝒢i.IsFinitePresentation]
      (φ ψ : ℱi ⟶ 𝒢i)
      (hφψ : (Scheme.Modules.pullback (c.π.app i)).map φ =
        (Scheme.Modules.pullback (c.π.app i)).map ψ),
      ∃ (i' : I) (hii' : i ≤ i'),
        (Scheme.Modules.pullback (D.map (homOfLE hii'))).map φ =
          (Scheme.Modules.pullback (D.map (homOfLE hii'))).map ψ)
