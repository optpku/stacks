module

public import stacks_project.Chap70.Lemma_70_7_1_FinitePresentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 70.7.1 (1): every algebraic space of finite presentation over the limit
descends to an algebraic space of finite presentation over some stage, up to
isomorphism over the limit. -/
@[stacks 07SK] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.FinitePresentation.exists_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
      (c : Cone D) (hc : IsLimit c)
      [∀ j, IsQuasiCompact (D.obj j)]
      [∀ j, IsQuasiSeparated (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
      (Y : Over c.pt) [FinitePresentation Y.hom],
      ∃ (i : I) (Yi : Over (D.obj i)),
        FinitePresentation Yi.hom ∧
          Nonempty ((Over.pullback (c.π.app i)).obj Yi ≅ Y))

/- Lemma 70.7.1 (2): a morphism between the limit pullbacks of two algebraic
spaces of finite presentation over one stage descends to a morphism over some
later stage. -/
@[stacks 07SK] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.FinitePresentation.exists_hom_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
      (c : Cone D) (hc : IsLimit c)
      [∀ j, IsQuasiCompact (D.obj j)]
      [∀ j, IsQuasiSeparated (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
      (i : I) (Yi Zi : Over (D.obj i))
      [FinitePresentation Yi.hom] [FinitePresentation Zi.hom]
      (φ : (Over.pullback (c.π.app i)).obj Yi ⟶
        (Over.pullback (c.π.app i)).obj Zi),
      ∃ (i' : I) (hii' : i ≤ i')
        (hcomp : c.π.app i' ≫ D.map (homOfLE hii') = c.π.app i)
        (φi' : (Over.pullback (D.map (homOfLE hii'))).obj Yi ⟶
          (Over.pullback (D.map (homOfLE hii'))).obj Zi),
        (Over.pullbackComp (c.π.app i') (D.map (homOfLE hii'))).hom.app Yi ≫
            (Over.pullback (c.π.app i')).map φi' ≫
          (Over.pullbackComp (c.π.app i') (D.map (homOfLE hii'))).inv.app Zi =
          eqToHom (congrArg (fun F : Over (D.obj i) ⥤ Over c.pt ↦ F.obj Yi)
            (Over.pullback.congr_simp (c.π.app i' ≫ D.map (homOfLE hii'))
              (c.π.app i) hcomp)) ≫
            φ ≫
          eqToHom (Eq.symm (congrArg (fun F : Over (D.obj i) ⥤ Over c.pt ↦ F.obj Zi)
            (Over.pullback.congr_simp (c.π.app i' ≫ D.map (homOfLE hii'))
              (c.π.app i) hcomp))))

/- Lemma 70.7.1 (3): two morphisms between algebraic spaces of finite presentation
over one stage that agree after pullback to the limit agree after pullback to
some later stage. -/
@[stacks 07SK] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.FinitePresentation.exists_eq_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
      (c : Cone D) (hc : IsLimit c)
      [∀ j, IsQuasiCompact (D.obj j)]
      [∀ j, IsQuasiSeparated (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
      (i : I) (Yi Zi : Over (D.obj i))
      [FinitePresentation Yi.hom] [FinitePresentation Zi.hom]
      (φ ψ : Yi ⟶ Zi)
      (hφψ : (Over.pullback (c.π.app i)).map φ =
        (Over.pullback (c.π.app i)).map ψ),
      ∃ (i' : I) (hii' : i ≤ i'),
        (Over.pullback (D.map (homOfLE hii'))).map φ =
          (Over.pullback (D.map (homOfLE hii'))).map ψ)
