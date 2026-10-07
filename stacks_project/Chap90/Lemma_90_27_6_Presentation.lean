module

public import Mathlib.CategoryTheory.Category.ULift
public import stacks_project.Chap90.Definition_90_16_8
public import stacks_project.Chap90.Lemma_90_25_2
public import stacks_project.Chap90.«90_7_12_1_Yoneda»
public import stacks_project.Chap90.Remarks_90_5_2_Grothendieck

/-!
# Kernel-pair presentation of a formal object

A formal object of the Hom-universe lift of a category cofibered in groupoids `G`
determines the associated morphism `underline ξ : underline R |_{C_Λ} ⟶ G` and the
kernel-pair groupoid in functors of Lemma 90.25.2.
-/

@[expose] public section

open CategoryTheory CompleteLocalAlgCat
open CofiberedCategoryOver.Groupoids
open scoped BasedFunctor

noncomputable section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {G : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
    (ArtinianLocalAlgCat Λ k)}

namespace CategoryTheory.CofiberedCategoryOver.Groupoids

/-- Projection of the Hom-universe lift of `G` to `ArtinianLocalAlgCat Λ k`. -/
def liftProjection : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k :=
  ULiftHom.down ⋙ G.p

/-- `liftProjection` is `ULiftHom.down` followed by the projection of `G`. -/
theorem liftProjection_eq : liftProjection = ULiftHom.down ⋙ G.p := sorry

/-- The Hom-universe lift of a category cofibered in groupoids is again cofibered in
groupoids. -/
instance instIsFiberedInGroupoids_liftProjection :
    Functor.IsFibered.InGroupoids (ULiftHom.down ⋙ G.p).op := sorry

/-- The based functor `ULiftHom.down` over `ArtinianLocalAlgCat Λ k`. -/
def downBased :
    BasedCategory.ofFunctor
        (ULiftHom.down ⋙ G.p : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k) ⥤ᵇ
      G.toBasedCategory :=
  BasedFunctor.ofFunctor ULiftHom.down rfl

/-- The underlying functor of `downBased` is `ULiftHom.down`. -/
theorem downBased_toFunctor :
    downBased.toFunctor =
      (ULiftHom.down : ULiftHom.{u + 1} G.total ⥤ G.total) := sorry

end CategoryTheory.CofiberedCategoryOver.Groupoids

namespace FormalObject

/-- The associated morphism `underline ξ : underline R |_{C_Λ} ⟶ G` of Remark 90.7.12,
as a based functor from the category of elements of `restrictedCoyoneda ξ.base`. -/
def associatedMorphism
    (ξ : FormalObject
      (ULiftHom.down ⋙ G.p : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k)) :
    RestrictedHom
      (ULiftHom.down ⋙ G.p : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k) ξ.base :=
  (fromRestrictedHom
        (ULiftHom.down ⋙ G.p : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k)
        ξ.base).inv.obj
    ⟨ξ, rfl⟩

/-- Evaluating `associatedMorphism ξ` on identity truncations recovers `ξ` in the
completion fibre. -/
def associatedMorphism_spec
    (ξ : FormalObject
      (ULiftHom.down ⋙ G.p : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k)) :
    (fromRestrictedHom
          (ULiftHom.down ⋙ G.p : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k)
          ξ.base).obj
        (associatedMorphism ξ) ≅ ⟨ξ, rfl⟩ :=
  (fromRestrictedHom
        (ULiftHom.down ⋙ G.p : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k)
        ξ.base).objObjPreimageIso ⟨ξ, rfl⟩

/-- The associated morphism as a morphism of categories cofibered in groupoids from
`ofTypeValued (restrictedCoyoneda ξ.base)` to `G`, obtained by composing with
`ULiftHom.down`. -/
def associatedMorphismOver
    (ξ : FormalObject
      (ULiftHom.down ⋙ G.p : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k)) :
    Functor.ofTypeValued.{u + 1, u, u} (restrictedCoyoneda ξ.base) ⟶ G :=
  ofBasedFunctor
    (BasedFunctor.comp
      (associatedMorphism ξ :
        BasedCategory.ofFunctor (CategoryOfElements.π (restrictedCoyoneda ξ.base)) ⥤ᵇ
          BasedCategory.ofFunctor
            (ULiftHom.down ⋙ G.p :
              ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k))
      downBased)

/-- `associatedMorphism ξ` is the inverse-image of `ξ` under `fromRestrictedHom`. -/
theorem associatedMorphism_eq
    (ξ : FormalObject
      (ULiftHom.down ⋙ G.p : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k)) :
    associatedMorphism ξ =
      (fromRestrictedHom
            (ULiftHom.down ⋙ G.p : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k)
            ξ.base).inv.obj
        ⟨ξ, rfl⟩ := sorry

/-- `associatedMorphismOver` is `associatedMorphism` followed by `downBased`. -/
theorem associatedMorphismOver_comp
    (ξ : FormalObject
      (ULiftHom.down ⋙ G.p : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k)) :
    toBasedFunctor (associatedMorphismOver ξ) =
      BasedFunctor.comp
        (associatedMorphism ξ :
          BasedCategory.ofFunctor (CategoryOfElements.π (restrictedCoyoneda ξ.base)) ⥤ᵇ
            BasedCategory.ofFunctor
              (ULiftHom.down ⋙ G.p :
                ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k))
        downBased := sorry

end FormalObject

namespace CategoryTheory.GroupoidInFunctors

/-- The kernel-pair groupoid in functors of Lemma 90.25.2 attached to
`associatedMorphismOver ξ`. -/
def ofFormalObject
    (ξ : FormalObject
      (ULiftHom.down ⋙ G.p : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k)) :
    GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k) :=
  ofMorphism.{u + 1, u, u} (FormalObject.associatedMorphismOver ξ)

/-- `ofFormalObject ξ` is the kernel-pair groupoid of `associatedMorphismOver ξ`. -/
theorem ofFormalObject_eq_ofMorphism
    (ξ : FormalObject
      (ULiftHom.down ⋙ G.p : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k)) :
    ofFormalObject ξ = ofMorphism.{u + 1, u, u} (FormalObject.associatedMorphismOver ξ) :=
  sorry

/-- The object functor of `ofFormalObject ξ` is `restrictedCoyoneda ξ.base`. -/
theorem ofFormalObject_U
    (ξ : FormalObject
      (ULiftHom.down ⋙ G.p : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k)) :
    (ofFormalObject ξ).U = restrictedCoyoneda ξ.base := sorry

/-- The arrow functor of `ofFormalObject ξ` is the kernel pair of
`associatedMorphismOver ξ`. -/
theorem ofFormalObject_relation
    (ξ : FormalObject
      (ULiftHom.down ⋙ G.p : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k)) :
    (ofFormalObject ξ).R = relation (FormalObject.associatedMorphismOver ξ) := sorry

end CategoryTheory.GroupoidInFunctors

end
