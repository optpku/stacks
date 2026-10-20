module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.SchemeBaseChange
public import ReasLib.AlgebraicGeometry.GroupoidsOver.SmoothOnSchemes
public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# Smoothness and scheme base-change compatibility

The scheme representation and smoothness criteria retain their complete types
through the canonical mathematical owners.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (overMap)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

#check (AlgebraicGeometry.Groupoids.Hom.RepresentsSchemeBaseChange :
    ∀ {B : Scheme.{u}} {X Y : GroupoidsOver B}
    (f : X ⟶ Y) {U : Over B} (y : GroupoidsOver.slice U ⟶ Y) (W : Over B)
    (π : W ⟶ U),
    Prop)

#check (AlgebraicGeometry.Groupoids.Hom.RepresentsSchemeBaseChange.apex_equivalence :
    ∀ {B : Scheme.{u}}
    {X Y : GroupoidsOver B} {f : X ⟶ Y} {U : Over B}
    {y : GroupoidsOver.slice U ⟶ Y} {W : Over B} {π : W ⟶ U}
    (h : RepresentsSchemeBaseChange f y W π),
    Nonempty (TwoFibreProduct.apex.{u + 1, u, u + 1, u} y f ≌
      GroupoidsOver.slice W))

#check (AlgebraicGeometry.Groupoids.Hom.RepresentsSchemeBaseChange.projection_triangle :
    ∀ {B : Scheme.{u}}
    {X Y : GroupoidsOver B} {f : X ⟶ Y} {U : Over B}
    {y : GroupoidsOver.slice U ⟶ Y} {W : Over B} {π : W ⟶ U}
    (h : RepresentsSchemeBaseChange f y W π),
    ∃ e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} y f ≌ GroupoidsOver.slice W,
      Nonempty
        (e.hom ≫ overMap π ≅ TwoFibreProduct.fst.{u + 1, u, u + 1, u} y f))

#check (AlgebraicGeometry.Groupoids.Hom.RepresentsSchemeBaseChange.iff :
    ∀ {B : Scheme.{u}} {X Y : GroupoidsOver B}
    {f : X ⟶ Y} {U : Over B} {y : GroupoidsOver.slice U ⟶ Y} {W : Over B}
    {π : W ⟶ U},
    RepresentsSchemeBaseChange f y W π ↔
      ∃ e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} y f ≌ GroupoidsOver.slice W,
        Nonempty
          (e.hom ≫ overMap π ≅ TwoFibreProduct.fst.{u + 1, u, u + 1, u} y f))

#check (AlgebraicGeometry.Groupoids.Hom.SmoothOnSchemes :
    ∀ {B : Scheme.{u}} {X : GroupoidsOver B} {S : Over B}
    (f : GroupoidsOver.slice S ⟶ X),
    Prop)

#check (AlgebraicGeometry.Groupoids.Hom.SmoothOnSchemes.id :
    ∀ {B : Scheme.{u}} {S : Over B},
    SmoothOnSchemes (𝟙 (GroupoidsOver.slice S)))

#check (AlgebraicGeometry.Groupoids.Hom.SmoothOnSchemes.ofSmooth :
    ∀ {B : Scheme.{u}} {S T : Over B} (h : S ⟶ T)
    [AlgebraicGeometry.Smooth h.left],
    SmoothOnSchemes (overMap h))

#check (AlgebraicGeometry.Groupoids.Hom.SmoothOnSchemes.spec :
    ∀ {B : Scheme.{u}} {X : GroupoidsOver B} {S : Over B}
    (f : GroupoidsOver.slice S ⟶ X) [SmoothOnSchemes f] {S' : Over B}
    (g : GroupoidsOver.slice S' ⟶ X) {W : Over B} {π : W ⟶ S'}
    (h : RepresentsSchemeBaseChange f g W π),
    AlgebraicGeometry.Smooth π.left)

#check (AlgebraicGeometry.Groupoids.Hom.SmoothOnSchemes.relativelyRepresentable :
    ∀ {B : Scheme.{u}} {X : GroupoidsOver B}
    {S : Over B} (f : GroupoidsOver.slice S ⟶ X) [SmoothOnSchemes f],
    FiberedCategoryOver.Groupoids.relativelyRepresentable f)

#check (AlgebraicGeometry.Groupoids.Hom.SmoothOnSchemes.of :
    ∀ {B : Scheme.{u}} {X : GroupoidsOver B} {S : Over B}
    {f : GroupoidsOver.slice S ⟶ X}
    (hrep : FiberedCategoryOver.Groupoids.relativelyRepresentable f)
    (hsm : ∀ ⦃S' : Over B⦄ (g : GroupoidsOver.slice S' ⟶ X)
      (W : Over B) (π : W ⟶ S'),
      RepresentsSchemeBaseChange f g W π → AlgebraicGeometry.Smooth π.left),
    SmoothOnSchemes f)

#check (AlgebraicGeometry.Groupoids.Hom.SmoothOnSchemes.iff :
    ∀ {B : Scheme.{u}} {X : GroupoidsOver B} {S : Over B}
    (f : GroupoidsOver.slice S ⟶ X),
    SmoothOnSchemes f ↔
      FiberedCategoryOver.Groupoids.relativelyRepresentable f ∧
        ∀ ⦃S' : Over B⦄ (g : GroupoidsOver.slice S' ⟶ X) (W : Over B)
          (π : W ⟶ S'),
          RepresentsSchemeBaseChange f g W π →
            AlgebraicGeometry.Smooth π.left)

end AlgebraicGeometry.Groupoids.Hom
