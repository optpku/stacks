module

public import ReasLib.CategoryTheory.Cofibered.ULiftHom
public import ReasLib.CategoryTheory.Cofibered.Grothendieck
public import ReasLib.CategoryTheory.Groupoid.KernelPair
public import ReasLib.AlgebraicGeometry.FormalDeformation.RestrictedHom
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Versal

/-!
# Associated morphisms of formal objects

Restricted-Yoneda evaluation associates a morphism to each formal object.
Its kernel pair gives a groupoid in functors with the restricted coyoneda as
its object functor.
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

/-- The based functor `ULiftHom.down` over `ArtinianLocalAlgCat Λ k`. -/
def downBased :
    BasedCategory.ofFunctor
        (ULiftHom.down ⋙ G.p : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k) ⥤ᵇ
      G.toBasedCategory :=
  BasedFunctor.ofFunctor ULiftHom.down rfl

/-- The underlying functor of `downBased` is `ULiftHom.down`. -/
theorem downBased_toFunctor :
    downBased.toFunctor =
      (ULiftHom.down : ULiftHom.{u + 1} G.total ⥤ G.total) := rfl

end CategoryTheory.CofiberedCategoryOver.Groupoids

namespace FormalObject

/-- The associated morphism is the restricted-Yoneda inverse image of a formal object. -/
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
        downBased := rfl

/-- The associated morphism of a versal formal object is smooth. -/
theorem associatedMorphismOver_isSmooth
    (ξ : FormalObject
      (ULiftHom.down ⋙ G.p : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k))
    [IsVersal ξ] :
    BasedFunctor.IsSmooth (toBasedFunctor (associatedMorphismOver ξ)) := sorry

end FormalObject

namespace CategoryTheory.GroupoidInFunctors

/-- The kernel-pair groupoid of the associated morphism of a formal object. -/
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
  rfl

/-- The object functor of `ofFormalObject ξ` is `restrictedCoyoneda ξ.base`. -/
theorem ofFormalObject_U
    (ξ : FormalObject
      (ULiftHom.down ⋙ G.p : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k)) :
    (ofFormalObject ξ).U = restrictedCoyoneda ξ.base := rfl

/-- The arrow functor of `ofFormalObject ξ` is the kernel pair of
`associatedMorphismOver ξ`. -/
theorem ofFormalObject_relation
    (ξ : FormalObject
      (ULiftHom.down ⋙ G.p : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k)) :
    (ofFormalObject ξ).R = relation (FormalObject.associatedMorphismOver ξ) := rfl

end CategoryTheory.GroupoidInFunctors

end
