/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Limit.FinitePresentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 70.7.2 (1): finitely presented modules on the limit of a directed affine
inverse system of quasi-compact, quasi-separated algebraic spaces descend to a
finitely presented module at some stage. -/
@[stacks 07V7] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Limit.FinitePresentation.exists_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
      (c : Cone D) (hc : IsLimit c)
      [∀ j, IsQuasiCompact (D.obj j)]
      [∀ j, IsAbsolutelyQuasiSeparated (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
      (ℱ : c.pt.Modules) [ℱ.IsFinitePresentation],
      ∃ (i : I) (ℱi : (D.obj i).Modules),
        ℱi.IsFinitePresentation ∧
          Nonempty ((Modules.pullback (c.π.app i)).obj ℱi ≅ ℱ))

/- Lemma 70.7.2 (2): a morphism between the limit pullbacks of two finitely
presented modules over one stage descends to a morphism over some later stage. -/
@[stacks 07V7] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Limit.FinitePresentation.exists_hom_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
      (c : Cone D) (hc : IsLimit c)
      [∀ j, IsQuasiCompact (D.obj j)]
      [∀ j, IsAbsolutelyQuasiSeparated (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
      (i : I) (ℱi 𝒢i : (D.obj i).Modules)
      [ℱi.IsFinitePresentation] [𝒢i.IsFinitePresentation]
      (φ : (Modules.pullback (c.π.app i)).obj ℱi ⟶
        (Modules.pullback (c.π.app i)).obj 𝒢i),
      ∃ (i' : I) (hii' : i ≤ i')
        (hcomp : c.π.app i' ≫ D.map (homOfLE hii') = c.π.app i)
        (φi' : (Modules.pullback (D.map (homOfLE hii'))).obj ℱi ⟶
          (Modules.pullback (D.map (homOfLE hii'))).obj 𝒢i),
        (Modules.pullbackCompIso (c.π.app i') (D.map (homOfLE hii'))).inv.app ℱi ≫
            (Modules.pullback (c.π.app i')).map φi' ≫
          (Modules.pullbackCompIso (c.π.app i') (D.map (homOfLE hii'))).hom.app 𝒢i =
          (Modules.pullbackCongr hcomp).hom.app ℱi ≫ φ ≫
            (Modules.pullbackCongr hcomp).inv.app 𝒢i)

/- Lemma 70.7.2 (3): two morphisms between finitely presented modules over one
stage that agree after pullback to the limit agree after pullback to some later
stage. -/
@[stacks 07V7] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Limit.FinitePresentation.exists_eq_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
      (c : Cone D) (hc : IsLimit c)
      [∀ j, IsQuasiCompact (D.obj j)]
      [∀ j, IsAbsolutelyQuasiSeparated (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
      (i : I) (ℱi 𝒢i : (D.obj i).Modules)
      [ℱi.IsFinitePresentation] [𝒢i.IsFinitePresentation]
      (φ ψ : ℱi ⟶ 𝒢i)
      (hφψ : (Modules.pullback (c.π.app i)).map φ =
        (Modules.pullback (c.π.app i)).map ψ),
      ∃ (i' : I) (hii' : i ≤ i'),
        (Modules.pullback (D.map (homOfLE hii'))).map φ =
          (Modules.pullback (D.map (homOfLE hii'))).map ψ)
