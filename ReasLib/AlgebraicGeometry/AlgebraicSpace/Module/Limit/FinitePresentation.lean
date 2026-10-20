module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Equality

/-!
# Finitely presented modules over inverse limits of algebraic spaces

Finitely presented modules and their morphisms descend along directed inverse limits
of quasi-compact, absolutely quasi-separated algebraic spaces with affine transition
maps. Equality of morphisms after pullback to the limit is detected at a later stage.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.Limit.FinitePresentation

/-- A finitely presented module on a directed inverse limit of quasi-compact,
absolutely quasi-separated algebraic spaces with affine transition maps descends to a finitely
presented module at some stage. -/
theorem exists_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D) (hc : IsLimit c)
    [∀ j, IsQuasiCompact (D.obj j)]
    [∀ j, IsAbsolutelyQuasiSeparated (D.obj j)]
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
    [∀ j, IsAbsolutelyQuasiSeparated (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    (i : I) (ℱi 𝒢i : (D.obj i).Modules)
    [ℱi.IsFinitePresentation] [𝒢i.IsFinitePresentation]
    (φ : (Modules.pullback (c.π.app i)).obj ℱi ⟶
      (Modules.pullback (c.π.app i)).obj 𝒢i) :
    ∃ (i' : I) (hii' : i ≤ i')
      (hcomp : c.π.app i' ≫ D.map (homOfLE hii') = c.π.app i)
      (φi' : (Modules.pullback (D.map (homOfLE hii'))).obj ℱi ⟶
        (Modules.pullback (D.map (homOfLE hii'))).obj 𝒢i),
      (Modules.pullbackCompIso (c.π.app i') (D.map (homOfLE hii'))).inv.app ℱi ≫
          (Modules.pullback (c.π.app i')).map φi' ≫
        (Modules.pullbackCompIso (c.π.app i') (D.map (homOfLE hii'))).hom.app 𝒢i =
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
    [∀ j, IsAbsolutelyQuasiSeparated (D.obj j)]
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
