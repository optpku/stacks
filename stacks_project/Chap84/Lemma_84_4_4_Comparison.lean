/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.BaseChange
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_18_8_Topos

/-!
# Small étale base-change comparison of algebraic spaces

The inverse-image square of a cartesian diagram of algebraic spaces, and the
objectwise Beck–Chevalley mate `g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F` on small étale
topoi.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

section

variable {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)

/-- The inverse-image identification `g⁻¹ ⋙ f'⁻¹ ≅ f⁻¹ ⋙ g'⁻¹` of a cartesian
square of algebraic spaces. -/
def smallEtaleInverseImageSquare :
    (smallEtaleMorphismOfTopoi g).inverseImage ⋙
        (smallEtaleMorphismOfTopoi f').inverseImage ≅
      (smallEtaleMorphismOfTopoi f).inverseImage ⋙
        (smallEtaleMorphismOfTopoi g').inverseImage :=
  (smallEtaleMorphismOfTopoiComp f' g).symm ≪≫
    eqToIso (congrArg (fun h ↦ (smallEtaleMorphismOfTopoi h).inverseImage)
      h_cart.w.symm) ≪≫
    smallEtaleMorphismOfTopoiComp g' f

/-- `smallEtaleInverseImageSquare` is `smallEtaleMorphismOfTopoiComp` conjugated
by the commutativity of the cartesian square. -/
theorem smallEtaleInverseImageSquare_eq :
    smallEtaleInverseImageSquare f g f' g' h_cart =
      (smallEtaleMorphismOfTopoiComp f' g).symm ≪≫
        eqToIso (congrArg (fun h ↦ (smallEtaleMorphismOfTopoi h).inverseImage)
          h_cart.w.symm) ≪≫
        smallEtaleMorphismOfTopoiComp g' f :=
  sorry

variable (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))

/-- The adjunction-mate comparison `g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F` of a cartesian
square of algebraic spaces. -/
def smallEtaleBaseChangeHom :
    (smallEtaleMorphismOfTopoi g).inverseImage.obj
      ((smallEtaleMorphismOfTopoi f).pushforward.obj F) ⟶
      (smallEtaleMorphismOfTopoi f').pushforward.obj
        ((smallEtaleMorphismOfTopoi g').inverseImage.obj F) :=
  (MorphismOfTopoiIn.baseChange (smallEtaleMorphismOfTopoi g')
      (smallEtaleMorphismOfTopoi f') (smallEtaleMorphismOfTopoi f)
      (smallEtaleMorphismOfTopoi g)
      (smallEtaleInverseImageSquare f g f' g' h_cart).hom).app F

/-- `smallEtaleBaseChangeHom` is the objectwise mate of the inverse-image
square. -/
theorem smallEtaleBaseChangeHom_eq :
    smallEtaleBaseChangeHom f g f' g' h_cart F =
      (MorphismOfTopoiIn.baseChange (smallEtaleMorphismOfTopoi g')
          (smallEtaleMorphismOfTopoi f') (smallEtaleMorphismOfTopoi f)
          (smallEtaleMorphismOfTopoi g)
          (smallEtaleInverseImageSquare f g f' g' h_cart).hom).app F :=
  sorry

end

section

variable {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
variable (f : X ⟶ Y) (g : Y' ⟶ Y)
variable (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))

/-- The comparison morphism of the chosen fibre product `Y' ×_Y X`. -/
def smallEtaleBaseChangeHom_pullback :
    (smallEtaleMorphismOfTopoi g).inverseImage.obj
      ((smallEtaleMorphismOfTopoi f).pushforward.obj F) ⟶
      (smallEtaleMorphismOfTopoi (pullback.fst g f)).pushforward.obj
        ((smallEtaleMorphismOfTopoi (pullback.snd g f)).inverseImage.obj F) :=
  smallEtaleBaseChangeHom f g (pullback.fst g f) (pullback.snd g f)
    (IsPullback.of_hasPullback g f).flip F

/-- `smallEtaleBaseChangeHom_pullback` is `smallEtaleBaseChangeHom` at the
chosen pullback square. -/
theorem smallEtaleBaseChangeHom_pullback_eq :
    smallEtaleBaseChangeHom_pullback f g F =
      smallEtaleBaseChangeHom f g (pullback.fst g f) (pullback.snd g f)
        (IsPullback.of_hasPullback g f).flip F :=
  sorry

end

end AlgebraicGeometry.AlgebraicSpace
