/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import stacks_project.Chap92.«92_25_1_1_Site»

/-!
# The forgetful functor `forgetZariski` is fibered

Cartesian lifts of morphisms in `X.smallZariskiSite` keep the affine space fixed
and compose the open into the existing map to affine space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CotangentSite

/-- The cartesian lift of `f : U' ⟶ forgetZariski.obj P` obtained by composing
`U' ⟶ U ⟶ A`, keeping the polynomial affine space of `P` fixed. -/
def restrict {Λ : CommRingCat.{u}} {X : Scheme.{u}} [X.Over (Spec Λ)] (P : Obj Λ X)
    {U' : X.smallZariskiSite} (f : U' ⟶ (forgetZariski Λ X).obj P) : Obj Λ X where
  U := U'
  vars := P.vars
  hom := f.left ≫ P.hom
  w := sorry

/-- The open of `restrict P f` is the domain of `f`. -/
theorem restrict_U {Λ : CommRingCat.{u}} {X : Scheme.{u}} [X.Over (Spec Λ)] (P : Obj Λ X)
    {U' : X.smallZariskiSite} (f : U' ⟶ (forgetZariski Λ X).obj P) :
    (restrict P f).U = U' :=
  sorry

/-- Restriction keeps the polynomial variable type of `P`. -/
theorem restrict_vars {Λ : CommRingCat.{u}} {X : Scheme.{u}} [X.Over (Spec Λ)] (P : Obj Λ X)
    {U' : X.smallZariskiSite} (f : U' ⟶ (forgetZariski Λ X).obj P) :
    (restrict P f).vars = P.vars :=
  sorry

/-- The affine-space morphism of `restrict P f` is the composition `f.left ≫ P.hom`. -/
theorem restrict_hom {Λ : CommRingCat.{u}} {X : Scheme.{u}} [X.Over (Spec Λ)] (P : Obj Λ X)
    {U' : X.smallZariskiSite} (f : U' ⟶ (forgetZariski Λ X).obj P) :
    (restrict P f).hom = f.left ≫ P.hom :=
  sorry

/-- The comparison morphism `restrict P f ⟶ P` over `f`, identity on the affine space. -/
def restrictHom {Λ : CommRingCat.{u}} {X : Scheme.{u}} [X.Over (Spec Λ)] (P : Obj Λ X)
    {U' : X.smallZariskiSite} (f : U' ⟶ (forgetZariski Λ X).obj P) : restrict P f ⟶ P where
  left := f
  right := 𝟙 P.A
  isOver := sorry
  w := sorry

/-- The Zariski component of `restrictHom P f` is `f`. -/
theorem restrictHom_left {Λ : CommRingCat.{u}} {X : Scheme.{u}} [X.Over (Spec Λ)] (P : Obj Λ X)
    {U' : X.smallZariskiSite} (f : U' ⟶ (forgetZariski Λ X).obj P) :
    (restrictHom P f).left = f :=
  sorry

/-- The affine-space component of `restrictHom P f` is the identity. -/
theorem restrictHom_right {Λ : CommRingCat.{u}} {X : Scheme.{u}} [X.Over (Spec Λ)] (P : Obj Λ X)
    {U' : X.smallZariskiSite} (f : U' ⟶ (forgetZariski Λ X).obj P) :
    (restrictHom P f).right = 𝟙 P.A :=
  sorry

/-- The comparison `restrictHom P f` is strongly cartesian over `f`. -/
instance restrictHom_isStronglyCartesian {Λ : CommRingCat.{u}} {X : Scheme.{u}} [X.Over (Spec Λ)]
    (P : Obj Λ X) {U' : X.smallZariskiSite} (f : U' ⟶ (forgetZariski Λ X).obj P) :
    (forgetZariski Λ X).IsStronglyCartesian f (restrictHom P f) :=
  sorry

/-- The forgetful functor `forgetZariski Λ X` exhibits `Obj Λ X` as fibered over the small
Zariski site of `X`. -/
instance forgetZariski_isFibered (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    (forgetZariski Λ X).IsFibered :=
  sorry

end AlgebraicGeometry.Scheme.CotangentSite
