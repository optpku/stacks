/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.FinitePresentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

/- Lemma 32.10.1 (1): every scheme of finite presentation over the limit descends to a
scheme of finite presentation over some stage, up to isomorphism over the limit. -/
@[stacks 01ZM] #check
  (AlgebraicGeometry.Scheme.Limit.FinitePresentation.exists_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ j, CompactSpace (D.obj j).carrier]
      [∀ j, QuasiSeparatedSpace (D.obj j).carrier]
      [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
      (X : Over c.pt) (hX : Scheme.Hom.FinitePresentation X.hom),
      ∃ (i : I) (Xi : Over (D.obj i)),
        Scheme.Hom.FinitePresentation Xi.hom ∧
          Nonempty ((Over.pullback (c.π.app i)).obj Xi ≅ X))

/- Lemma 32.10.1 (2): a morphism between the limit pullbacks of two schemes of finite
presentation over one stage descends to a morphism over some later stage. -/
@[stacks 01ZM] #check
  (AlgebraicGeometry.Scheme.Limit.FinitePresentation.exists_hom_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ j, CompactSpace (D.obj j).carrier]
      [∀ j, QuasiSeparatedSpace (D.obj j).carrier]
      [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
      (i : I) (Xi Yi : Over (D.obj i))
      (hXi : Scheme.Hom.FinitePresentation Xi.hom)
      (hYi : Scheme.Hom.FinitePresentation Yi.hom)
      (φ : (Over.pullback (c.π.app i)).obj Xi ⟶
        (Over.pullback (c.π.app i)).obj Yi),
      ∃ (i' : I) (hii' : i ≤ i')
        (hcomp : c.π.app i' ≫ D.map (homOfLE hii') = c.π.app i)
        (φi' : (Over.pullback (D.map (homOfLE hii'))).obj Xi ⟶
          (Over.pullback (D.map (homOfLE hii'))).obj Yi),
        (Over.pullbackComp (c.π.app i') (D.map (homOfLE hii'))).hom.app Xi ≫
            (Over.pullback (c.π.app i')).map φi' ≫
          (Over.pullbackComp (c.π.app i') (D.map (homOfLE hii'))).inv.app Yi =
          eqToHom (congrArg (fun F : Over (D.obj i) ⥤ Over c.pt ↦ F.obj Xi)
            (Over.pullback.congr_simp (c.π.app i' ≫ D.map (homOfLE hii'))
              (c.π.app i) hcomp)) ≫
            φ ≫
          eqToHom (Eq.symm (congrArg (fun F : Over (D.obj i) ⥤ Over c.pt ↦ F.obj Yi)
            (Over.pullback.congr_simp (c.π.app i' ≫ D.map (homOfLE hii'))
              (c.π.app i) hcomp))))

/- Lemma 32.10.1 (3): two morphisms between schemes of finite presentation over one stage
that agree after pullback to the limit agree after pullback to some later stage. -/
@[stacks 01ZM] #check
  (AlgebraicGeometry.Scheme.Limit.FinitePresentation.exists_eq_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ j, CompactSpace (D.obj j).carrier]
      [∀ j, QuasiSeparatedSpace (D.obj j).carrier]
      [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
      (i : I) (Xi Yi : Over (D.obj i))
      (hXi : Scheme.Hom.FinitePresentation Xi.hom)
      (hYi : Scheme.Hom.FinitePresentation Yi.hom)
      (φ ψ : Xi ⟶ Yi)
      (hφψ : (Over.pullback (c.π.app i)).map φ =
        (Over.pullback (c.π.app i)).map ψ),
      ∃ (i' : I) (hii' : i ≤ i'),
        (Over.pullback (D.map (homOfLE hii'))).map φ =
          (Over.pullback (D.map (homOfLE hii'))).map ψ)
