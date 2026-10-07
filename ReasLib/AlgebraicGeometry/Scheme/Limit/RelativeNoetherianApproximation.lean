module

public import Mathlib.CategoryTheory.Limits.Final
public import ReasLib.AlgebraicGeometry.Scheme.Limit.AbsoluteNoetherianApproximation
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation.Yoneda
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Noetherian

/-!
# Relative Noetherian approximation

This file records simultaneous finite-type approximations of the source and target of a
morphism between quasi-compact, quasi-separated schemes.
-/

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Limit

/-- Every morphism between quasi-compact, quasi-separated schemes is recovered from a common
directed inverse system of morphisms between schemes of finite type over `ℤ`, with affine
transition morphisms on both the sources and the targets. -/
theorem exists_relativeNoetherianApproximation
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (Xsys Ssys : OrderDual I ⥤ Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
      (φ : Xsys ⟶ Ssys)
      (cX : Cone (Xsys ⋙ Over.forget (Spec (CommRingCat.of (ULift.{u} ℤ)))))
      (cS : Cone (Ssys ⋙ Over.forget (Spec (CommRingCat.of (ULift.{u} ℤ)))))
      (hcX : IsLimit cX) (hcS : IsLimit cS) (eX : X ≅ cX.pt) (eS : S ≅ cS.pt),
        (∀ i : I, eX.hom ≫ cX.π.app i ≫ (φ.app i).left =
          f ≫ eS.hom ≫ cS.π.app i) ∧
        (∀ {i i' : I} (hii' : i ≤ i'),
          IsAffineHom (Xsys.map (homOfLE hii')).left) ∧
        (∀ {i i' : I} (hii' : i ≤ i'),
          IsAffineHom (Ssys.map (homOfLE hii')).left) ∧
        (∀ i : I, Scheme.Hom.FiniteType (Xsys.obj i).hom) ∧
        ∀ i : I, Scheme.Hom.FiniteType (Ssys.obj i).hom := sorry

end AlgebraicGeometry.Scheme.Limit
