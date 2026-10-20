module

public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Bifunctor
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Comparison of fixed-right and bifunctorial Tor

The comparison between fixed-right derived tensoring and the two-variable derived tensor induces
an isomorphism on every Tor object.  This is the bridge used by fixed-right Tor-amplitude APIs.
-/

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe u v w

namespace CategoryTheory.DerivedCategory.DerivedTensor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [∀ G₁ G₂ : GradedObject ℤ C, GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ C,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [HomotopyCategory.Koszul.TensorDescends (C := C)]
variable [Bifunctor.Has (C := C)] [Right.Has (C := C)]

/-- Fixed-right Tor is naturally isomorphic to the fixed-right view of bifunctorial Tor. -/
@[stacks 08BP "fixed-right Tor functor comparison"]
noncomputable abbrev torRightFunctorIsoTor (p : ℕ) (L : DerivedCategory C)
    [Bifunctor.Right.Compatible L] :
    torRightFunctor p L ≅ Bifunctor.torRightFunctor p L :=
  Functor.isoWhiskerRight (Bifunctor.Right.iso L)
    (DerivedCategory.homologyFunctor C (-(p : ℤ)))

/-- Fixed-right Tor agrees with bifunctorial Tor on arbitrary derived objects. -/
@[stacks 08BP "fixed-right Tor comparison"]
noncomputable abbrev torRightObjIsoTor (p : ℕ) (K L : DerivedCategory C)
    [Bifunctor.Right.Compatible L] :
    torRightObj p K L ≅ Bifunctor.torObj p K L :=
  (torRightFunctorIsoTor p L).app K

/-- Fixed-right Tor agrees with bifunctorial Tor on objects placed in degree zero. -/
@[stacks 08BP "degree-zero fixed-right Tor comparison"]
noncomputable abbrev torRightIsoTor (p : ℕ) (F G : C)
    [Bifunctor.Right.Compatible ((DerivedCategory.singleFunctor C (0 : ℤ)).obj G)] :
    torRight p F G ≅ Bifunctor.tor p F G :=
  torRightObjIsoTor p ((DerivedCategory.singleFunctor C (0 : ℤ)).obj F)
    ((DerivedCategory.singleFunctor C (0 : ℤ)).obj G)

end CategoryTheory.DerivedCategory.DerivedTensor

end
