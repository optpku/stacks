/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap70.Lemma_70_5_6_GlobalSections

/-!
# Finite-presentation descent of modules along directed affine limits of algebraic spaces

This leaf records the comparison isomorphism for module pullback along equal
morphisms, together with the object, morphism, and equality descent clauses for
finitely presented modules on a directed inverse limit of quasi-compact,
quasi-separated algebraic spaces with affine transition maps.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- Pullbacks of module sheaves along equal morphisms of algebraic spaces are
isomorphic. -/
noncomputable def pullbackCongr {X Y : AlgebraicSpace S} {f g : X ⟶ Y} (h : f = g) :
    pullback f ≅ pullback g :=
  eqToIso (congrArg pullback h)

/-- The component of `pullbackCongr` at a module is the corresponding `eqToHom` of
objects. -/
theorem pullbackCongr_hom_app {X Y : AlgebraicSpace S} {f g : X ⟶ Y} (h : f = g)
    (ℱ : Y.Modules) :
    (pullbackCongr h).hom.app ℱ =
      eqToHom (congrArg (fun φ ↦ (pullback φ).obj ℱ) h) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.Modules.Limit.FinitePresentation

/-- A finitely presented module on a directed inverse limit of quasi-compact,
quasi-separated algebraic spaces with affine transition maps descends to a finitely
presented module at some stage. -/
theorem exists_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D) (hc : IsLimit c)
    [∀ j, IsQuasiCompact (D.obj j)]
    [∀ j, IsQuasiSeparated (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    (ℱ : c.pt.Modules) [ℱ.IsFinitePresentation] :
    ∃ (i : I) (ℱi : (D.obj i).Modules),
      ℱi.IsFinitePresentation ∧
        Nonempty ((Modules.pullback (c.π.app i)).obj ℱi ≅ ℱ) := sorry

/-- A morphism between pullbacks of finitely presented modules from one stage of a
directed affine inverse limit of algebraic spaces descends to a morphism after
passing to a later stage. -/
theorem exists_hom_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D) (hc : IsLimit c)
    [∀ j, IsQuasiCompact (D.obj j)]
    [∀ j, IsQuasiSeparated (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    (i : I) (ℱi 𝒢i : (D.obj i).Modules)
    [ℱi.IsFinitePresentation] [𝒢i.IsFinitePresentation]
    (φ : (Modules.pullback (c.π.app i)).obj ℱi ⟶
      (Modules.pullback (c.π.app i)).obj 𝒢i) :
    ∃ (i' : I) (hii' : i ≤ i')
      (hcomp : c.π.app i' ≫ D.map (homOfLE hii') = c.π.app i)
      (φi' : (Modules.pullback (D.map (homOfLE hii'))).obj ℱi ⟶
        (Modules.pullback (D.map (homOfLE hii'))).obj 𝒢i),
      (Modules.pullbackComp (c.π.app i') (D.map (homOfLE hii'))).inv.app ℱi ≫
          (Modules.pullback (c.π.app i')).map φi' ≫
        (Modules.pullbackComp (c.π.app i') (D.map (homOfLE hii'))).hom.app 𝒢i =
        (Modules.pullbackCongr hcomp).hom.app ℱi ≫ φ ≫
          (Modules.pullbackCongr hcomp).inv.app 𝒢i := sorry

/-- If two morphisms between finitely presented modules at one stage become equal
after pullback to a directed affine inverse limit of algebraic spaces, then their
pullbacks are equal at some later stage. -/
theorem exists_eq_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D) (hc : IsLimit c)
    [∀ j, IsQuasiCompact (D.obj j)]
    [∀ j, IsQuasiSeparated (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    (i : I) (ℱi 𝒢i : (D.obj i).Modules)
    [ℱi.IsFinitePresentation] [𝒢i.IsFinitePresentation]
    (φ ψ : ℱi ⟶ 𝒢i)
    (hφψ : (Modules.pullback (c.π.app i)).map φ =
      (Modules.pullback (c.π.app i)).map ψ) :
    ∃ (i' : I) (hii' : i ≤ i'),
      (Modules.pullback (D.map (homOfLE hii'))).map φ =
        (Modules.pullback (D.map (homOfLE hii'))).map ψ := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.Limit.FinitePresentation
