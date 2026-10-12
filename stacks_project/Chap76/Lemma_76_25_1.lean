/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap67.Lemma_67_48_1_IntegralClosure
public import stacks_project.Chap76.Lemma_76_25_1_Pullback

/-!
# Smooth pullback of integral closures of quasi-coherent algebras

For a smooth morphism of algebraic spaces, formation of the integral closure of the
structure sheaf in a quasi-coherent algebra commutes with pullback.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

/-- The pulled-back inclusion of the integral closure lands in locally integral
sections of the pulled-back algebra. -/
theorem pullback_inclusion_mem_locallyIntegral {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) (A : X.QcAlgebraUnder) (U : smallEtaleSite Y)
    (x : sectionRing ((pullback f).obj (integralClosure A)) U) :
    ((InducedCategory.Hom.hom
        ((pullback f).map (inclusion A)).hom.right).app (op U)).hom x ∈
      locallyIntegral ((pullback f).obj A) U :=
  sorry

/-- The underlying sheaf morphism of the comparison
`(pullback f).obj (integralClosure A) ⟶ integralClosure ((pullback f).obj A)`,
obtained by restricting the pulled-back inclusion to locally integral sections. -/
def toIntegralClosureRight {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) (A : X.QcAlgebraUnder) :
    sheaf ((pullback f).obj (integralClosure A)) ⟶
      sheaf (integralClosure ((pullback f).obj A)) :=
  InducedCategory.homMk
    { app := fun U ↦
        CommRingCat.ofHom
          (RingHom.codRestrict
            ((InducedCategory.Hom.hom
                ((pullback f).map (inclusion A)).hom.right).app U).hom
            (locallyIntegral ((pullback f).obj A) U.unop)
            (pullback_inclusion_mem_locallyIntegral f A U.unop))
      naturality := fun _ _ _ ↦ sorry }

/-- On sections, `toIntegralClosureRight` is the codomain restriction of the pulled-back
inclusion into locally integral sections. -/
theorem toIntegralClosureRight_app {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) (A : X.QcAlgebraUnder) (U : (smallEtaleSite Y)ᵒᵖ) :
    (InducedCategory.Hom.hom (toIntegralClosureRight f A)).app U =
      CommRingCat.ofHom
        (RingHom.codRestrict
          ((InducedCategory.Hom.hom
              ((pullback f).map (inclusion A)).hom.right).app U).hom
          (locallyIntegral ((pullback f).obj A) U.unop)
          (pullback_inclusion_mem_locallyIntegral f A U.unop)) :=
  rfl

/-- The structure morphism of the pulled-back integral closure factors through
`toIntegralClosureRight`. -/
theorem toIntegralClosureRight_w {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) (A : X.QcAlgebraUnder) :
    ((pullback f).obj (integralClosure A)).obj.hom ≫ toIntegralClosureRight f A =
      (integralClosure ((pullback f).obj A)).obj.hom :=
  sorry

/-- The canonical comparison from the pullback of the integral closure of `A` to the
integral closure of the pullback of `A`. -/
def toIntegralClosure {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) (A : X.QcAlgebraUnder) :
    (pullback f).obj (integralClosure A) ⟶ integralClosure ((pullback f).obj A) :=
  InducedCategory.homMk
    (Under.homMk (toIntegralClosureRight f A) (toIntegralClosureRight_w f A))

/-- The comparison `toIntegralClosure f A` is a morphism of quasi-coherent algebras whose
right-hand sheaf map is `toIntegralClosureRight f A`. -/
theorem toIntegralClosure_hom_right {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) (A : X.QcAlgebraUnder) :
    (toIntegralClosure f A).hom.right = toIntegralClosureRight f A :=
  rfl

/-- After composing with the inclusion of the integral closure of `(pullback f).obj A`, the
comparison recovers the pullback of the inclusion `A' ⊂ A`. -/
theorem toIntegralClosure_comp_inclusion {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) (A : X.QcAlgebraUnder) :
    toIntegralClosure f A ≫ inclusion ((pullback f).obj A) =
      (pullback f).map (inclusion A) :=
  sorry

/-- Lemma 76.25.1: Let `S` be a scheme. Let `f : Y ⟶ X` be a smooth morphism of algebraic
spaces over `S`. Let `A` be a quasi-coherent sheaf of `𝒪_X`-algebras. The integral closure
of `𝒪_Y` in `(pullback f).obj A` is equal to `(pullback f).obj (integralClosure A)`, where
`inclusion A` exhibits `integralClosure A ⊂ A` as the integral closure of `𝒪_X` in `A`.
The comparison `toIntegralClosure f A` is an isomorphism, and together with
`toIntegralClosure_comp_inclusion` it identifies the two algebras as the same
subalgebra of `(pullback f).obj A`. -/
@[stacks 082E, instance]
instance toIntegralClosure_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) [Smooth f] (A : X.QcAlgebraUnder) :
    IsIso (toIntegralClosure f A) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder
