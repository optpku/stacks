module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Square
public import ReasLib.CategoryTheory.Sites.Over.Adjunction
public import ReasLib.CategoryTheory.Sites.Over.Derived
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_27_1_Hom
public import stacks_project.Chap84.Lemma_84_6_6_InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FppfEtale.BaseChange

/-! # Canonical fppf/étale derived base change of algebraic spaces -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.FppfEtale
open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology

universe u

/- Lemma 84.6.6: the canonical inverse-image square and derived comparison. -/
#check (AlgebraicGeometry.AlgebraicSpace.FppfEtale.inverseImageSquareIso :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    aInverseAbPlus Y ⋙ Derived.Over.Plus.pullback (fppfTopology S) f ≅
      smallInverseImagePlus f ⋙ aInverseAbPlus X)

#check (AlgebraicGeometry.AlgebraicSpace.FppfEtale.derivedBaseChange :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Adjunction.Derived.Plus.right (sheafPushforward AddCommGrpCat.{u + 1} f) ⋙
        aInverseAbPlus Y ⟶
      aInverseAbPlus X ⋙ Derived.Over.Plus.pushforward (fppfTopology S) f)

#check (AlgebraicGeometry.AlgebraicSpace.FppfEtale.derivedBaseChangeApp :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})),
    (aInverseAbPlus Y).obj
        ((Adjunction.Derived.Plus.right (sheafPushforward AddCommGrpCat.{u + 1} f)).obj K) ⟶
      (Derived.Over.Plus.pushforward (fppfTopology S) f).obj ((aInverseAbPlus X).obj K))

end
