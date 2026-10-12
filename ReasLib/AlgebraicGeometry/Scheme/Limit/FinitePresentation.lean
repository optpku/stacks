/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

/-!
# Finite-presentation descent along directed affine limits

This leaf records the object, morphism, and equality descent clauses for
schemes of finite presentation over a directed inverse limit of quasi-compact,
quasi-separated schemes with affine transition maps.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Limit.FinitePresentation

/-- Two morphisms between finitely presented objects over one stage of a directed affine limit
that agree after pullback to the limit agree after pullback to some later stage. -/
theorem exists_eq_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j).carrier]
    [∀ j, QuasiSeparatedSpace (D.obj j).carrier]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (i : I) (Xi Yi : Over (D.obj i))
    (hXi : Scheme.Hom.FinitePresentation Xi.hom)
    (hYi : Scheme.Hom.FinitePresentation Yi.hom)
    (φ ψ : Xi ⟶ Yi)
    (hφψ : (Over.pullback (c.π.app i)).map φ =
      (Over.pullback (c.π.app i)).map ψ) :
    ∃ (i' : I) (hii' : i ≤ i'),
      (Over.pullback (D.map (homOfLE hii'))).map φ =
        (Over.pullback (D.map (homOfLE hii'))).map ψ := sorry

/-- A morphism between the limit pullbacks of two finitely presented objects over one stage of
a directed affine limit descends to some later stage. The comparison uses the canonical
pullback-composition isomorphism and the cone relation. -/
theorem exists_hom_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j).carrier]
    [∀ j, QuasiSeparatedSpace (D.obj j).carrier]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (i : I) (Xi Yi : Over (D.obj i))
    (hXi : Scheme.Hom.FinitePresentation Xi.hom)
    (hYi : Scheme.Hom.FinitePresentation Yi.hom)
    (φ : (Over.pullback (c.π.app i)).obj Xi ⟶ (Over.pullback (c.π.app i)).obj Yi) :
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
            (c.π.app i) hcomp))) := sorry

/-- Every finitely presented scheme over a directed affine limit of quasi-compact,
quasi-separated schemes descends to a finitely presented scheme over some stage, whose pullback
to the limit is isomorphic to the original scheme over the limit. -/
theorem exists_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j).carrier]
    [∀ j, QuasiSeparatedSpace (D.obj j).carrier]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (X : Over c.pt) (hX : Scheme.Hom.FinitePresentation X.hom) :
    ∃ (i : I) (Xi : Over (D.obj i)),
      Scheme.Hom.FinitePresentation Xi.hom ∧
        Nonempty ((Over.pullback (c.π.app i)).obj Xi ≅ X) := sorry

end AlgebraicGeometry.Scheme.Limit.FinitePresentation
