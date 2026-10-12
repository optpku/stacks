/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Limit.RelativeNoetherianApproximation
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 32.7.1: every morphism between quasi-compact, quasi-separated schemes is the limit of
a common directed inverse system of morphisms between schemes of finite type over `ℤ`, with
affine transition morphisms on both sources and targets. -/
@[stacks 0GS1] #check
  (AlgebraicGeometry.Scheme.Limit.exists_relativeNoetherianApproximation :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace X] [QuasiSeparatedSpace X]
      [CompactSpace S] [QuasiSeparatedSpace S],
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
          ∀ i : I, Scheme.Hom.FiniteType (Ssys.obj i).hom)
