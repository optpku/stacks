module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.HasLimits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Finite-presentation descent along directed affine limits of algebraic spaces

Object, morphism, and equality descent hold for
algebraic spaces of finite presentation over a directed inverse limit of
quasi-compact, absolutely quasi-separated algebraic spaces with affine transition maps.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Limit.FinitePresentation

/-- Every algebraic space of finite presentation over a directed affine limit of
quasi-compact, absolutely quasi-separated algebraic spaces descends to a finitely presented
algebraic space over some stage, whose pullback to the limit is isomorphic to the
original space over the limit. -/
theorem exists_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D) (hc : IsLimit c)
    [∀ j, IsQuasiCompact (D.obj j)]
    [∀ j, IsAbsolutelyQuasiSeparated (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    (Y : Over c.pt) [FinitePresentation Y.hom] :
    ∃ (i : I) (Yi : Over (D.obj i)),
      FinitePresentation Yi.hom ∧
        Nonempty ((Over.pullback (c.π.app i)).obj Yi ≅ Y) := sorry

/-- A morphism between the limit pullbacks of two finitely presented algebraic
spaces over one stage of a directed affine limit of quasi-compact, absolutely
quasi-separated algebraic spaces descends to some later stage.
The comparison uses the canonical pullback-composition isomorphism and the cone
relation. -/
theorem exists_hom_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D) (hc : IsLimit c)
    [∀ j, IsQuasiCompact (D.obj j)]
    [∀ j, IsAbsolutelyQuasiSeparated (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    (i : I) (Yi Zi : Over (D.obj i))
    [FinitePresentation Yi.hom] [FinitePresentation Zi.hom]
    (φ : (Over.pullback (c.π.app i)).obj Yi ⟶
      (Over.pullback (c.π.app i)).obj Zi) :
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
            (c.π.app i) hcomp))) := sorry

/-- Two morphisms between finitely presented algebraic spaces over one stage of a
directed affine limit of quasi-compact, absolutely quasi-separated algebraic
spaces that agree after pullback to the limit agree after pullback to some later
stage. -/
theorem exists_eq_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D) (hc : IsLimit c)
    [∀ j, IsQuasiCompact (D.obj j)]
    [∀ j, IsAbsolutelyQuasiSeparated (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    (i : I) (Yi Zi : Over (D.obj i))
    [FinitePresentation Yi.hom] [FinitePresentation Zi.hom]
    (φ ψ : Yi ⟶ Zi)
    (hφψ : (Over.pullback (c.π.app i)).map φ =
      (Over.pullback (c.π.app i)).map ψ) :
    ∃ (i' : I) (hii' : i ≤ i'),
      (Over.pullback (D.map (homOfLE hii'))).map φ =
        (Over.pullback (D.map (homOfLE hii'))).map ψ := sorry

end AlgebraicGeometry.AlgebraicSpace.Limit.FinitePresentation
