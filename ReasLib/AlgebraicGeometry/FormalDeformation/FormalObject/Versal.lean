module

public import Mathlib.CategoryTheory.Category.ULift
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.RestrictedHom
public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth

/-!
# Versality and minimal presentations of formal objects

Identity truncations evaluate prorepresentations to formal objects. A minimal
presentation is represented by a minimal versal formal object.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u

noncomputable section

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FormalObject

/-- The projection from the Hom-universe lift of a functor's category of elements. -/
def elementsProjectionULift (U : ArtinianLocalAlgCat Λ k ⥤ Type u) :
    ULiftHom.{u + 1} U.Elements ⥤ ArtinianLocalAlgCat Λ k :=
  ULiftHom.down ⋙ CategoryOfElements.π U

/-- A lifted category-of-elements projection is cofibered in groupoids. -/
instance elementsProjectionULift_op_inGroupoids (U : ArtinianLocalAlgCat Λ k ⥤ Type u) :
    Functor.IsFibered.InGroupoids (elementsProjectionULift U).op := sorry

end FormalObject

namespace CompleteLocalAlgCat

/-- The Hom-universe lift of the category of elements of a restricted coyoneda. -/
abbrev identityTotal (R : CompleteLocalAlgCat Λ k) : Type (u + 1) :=
  ULiftHom.{u + 1} (restrictedCoyoneda R).Elements

/-- The identity domain is the lifted category of elements of restricted coyoneda. -/
theorem identityTotal_eq (R : CompleteLocalAlgCat Λ k) :
    identityTotal R = ULiftHom.{u + 1} (restrictedCoyoneda R).Elements := rfl

/-- The projection of the lifted restricted coyoneda category of elements. -/
abbrev identityProjection (R : CompleteLocalAlgCat Λ k) :
    identityTotal R ⥤ ArtinianLocalAlgCat Λ k :=
  FormalObject.elementsProjectionULift (restrictedCoyoneda R)

/-- The identity projection forgets the Hom-universe lift and then the element. -/
theorem identityProjection_eq (R : CompleteLocalAlgCat Λ k) :
    identityProjection R =
      (ULiftHom.down : identityTotal R ⥤ (restrictedCoyoneda R).Elements) ⋙
        CategoryOfElements.π (restrictedCoyoneda R) := rfl

/-- The lifted identity element at the corresponding Artinian truncation. -/
def identityStage (R : CompleteLocalAlgCat Λ k) (n : ℕ) : identityTotal R :=
  ULiftHom.objUp (FormalObject.restrictedIdentity R n)

/-- An identity stage is the lift of the canonical identity truncation element. -/
theorem identityStage_eq (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    identityStage R n = ULiftHom.objUp (FormalObject.restrictedIdentity R n) := rfl

/-- The lifted successor map of canonical identity truncations. -/
def identityStageMap (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    identityStage R (n + 1) ⟶ identityStage R n :=
  (ULiftHom.up : (restrictedCoyoneda R).Elements ⥤ identityTotal R).map
    (FormalObject.restrictedIdentityMap R n)

/-- Identity successor maps are functorial lifts of the canonical successor projections. -/
theorem identityStageMap_eq (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    identityStageMap R n =
      (ULiftHom.up : (restrictedCoyoneda R).Elements ⥤ identityTotal R).map
        (FormalObject.restrictedIdentityMap R n) := rfl

/-- Identity successor maps lie over the corresponding Artinian truncation projections. -/
theorem identityFormalObject_over_step (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (identityProjection R).IsHomLift (R.truncationMap n) (identityStageMap R n) := sorry

/-- The formal object of a restricted coyoneda given by its canonical identity tower. -/
def identityFormalObject (R : CompleteLocalAlgCat Λ k) :
    FormalObject (identityProjection R) :=
  FormalObject.of R (identityStage R) (identityStageMap R) (fun _ ↦ rfl)
    (identityFormalObject_over_step R)

/-- The base of the identity formal object is its representing algebra. -/
theorem identityFormalObject_base (R : CompleteLocalAlgCat Λ k) :
    (identityFormalObject R).base = R := rfl

/-- Identity formal-object stages and transitions lie over the canonical truncation tower. -/
theorem identityFormalObject_spec (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (identityProjection R).obj ((identityFormalObject R).system.family n) = R.truncation n ∧
      (identityProjection R).IsHomLift (R.truncationMap n)
        ((identityFormalObject R).system.stepMap n) :=
  ⟨(identityFormalObject R).over_obj n, (identityFormalObject R).over_step n⟩

end CompleteLocalAlgCat

namespace FormalObject

variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/-- A based functor represents a formal object when its identity-tower evaluations
are vertically isomorphic to the stages, compatibly with successor transitions. -/
def Represents (ξ : FormalObject p)
    (φ : BasedCategory.ofFunctor (CompleteLocalAlgCat.identityProjection ξ.base) ⥤ᵇ
      BasedCategory.ofFunctor p) : Prop :=
  ∃ stageIso : ∀ n : ℕ,
      φ.obj (CompleteLocalAlgCat.identityStage ξ.base n) ≅ ξ.system.family n,
    (∀ n : ℕ, p.IsHomLift (𝟙 (ξ.base.truncation n)) (stageIso n).hom) ∧
      ∀ n : ℕ,
        φ.map (CompleteLocalAlgCat.identityStageMap ξ.base n) ≫ (stageIso n).hom =
          (stageIso (n + 1)).hom ≫ ξ.system.stepMap n

/-- Each identity-stage evaluation of a representing functor admits a vertical
isomorphism to the corresponding formal-object stage. -/
theorem represents_obj (ξ : FormalObject p)
    (φ : BasedCategory.ofFunctor (CompleteLocalAlgCat.identityProjection ξ.base) ⥤ᵇ
      BasedCategory.ofFunctor p) (representation : Represents ξ φ) (n : ℕ) :
    ∃ e : φ.obj (CompleteLocalAlgCat.identityStage ξ.base n) ≅ ξ.system.family n,
      p.IsHomLift (𝟙 (ξ.base.truncation n)) e.hom := sorry

/-- A formal object is versal when it admits a smooth representing based functor. -/
class IsVersal (ξ : FormalObject p) [Functor.IsFibered.InGroupoids p.op] : Prop where
  /-- A smooth based functor represents the formal object. -/
  exists_smooth_representation :
    ∃ φ : BasedCategory.ofFunctor (CompleteLocalAlgCat.identityProjection ξ.base) ⥤ᵇ
        BasedCategory.ofFunctor p,
      Represents ξ φ ∧ BasedFunctor.IsSmooth φ

/-- A versal formal object has a smooth representing based functor. -/
theorem IsVersal.spec (ξ : FormalObject p) [Functor.IsFibered.InGroupoids p.op]
    [versal : IsVersal ξ] :
    ∃ φ : BasedCategory.ofFunctor (CompleteLocalAlgCat.identityProjection ξ.base) ⥤ᵇ
        BasedCategory.ofFunctor p,
      Represents ξ φ ∧ BasedFunctor.IsSmooth φ := versal.exists_smooth_representation

/-- A versal formal object is minimal when every incoming formal-object map is surjective on bases. -/
class IsMinimalVersal (ξ : FormalObject p) [Functor.IsFibered.InGroupoids p.op] : Prop
    extends IsVersal ξ where
  /-- Every incoming formal-object map is surjective on the underlying complete local algebra. -/
  surjective_base : ∀ {η : FormalObject p} (morphism : η ⟶ ξ),
    Function.Surjective morphism.base.hom

/-- Incoming maps to a minimal versal formal object are surjective on complete local bases. -/
theorem IsMinimalVersal.spec (ξ : FormalObject p) [Functor.IsFibered.InGroupoids p.op]
    [minimal : IsMinimalVersal ξ] {η : FormalObject p} (morphism : η ⟶ ξ) :
    Function.Surjective morphism.base.hom := minimal.surjective_base morphism

/-- A prorepresentation induces a based functor from its lifted restricted coyoneda domain. -/
theorem prorepresentationFunctor_over (U : ArtinianLocalAlgCat Λ k ⥤ Type u)
    {R : CompleteLocalAlgCat Λ k} (e : U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) :
    (ULiftHom.down ⋙ CategoryOfElements.map e.inv ⋙ ULiftHom.up) ⋙
      elementsProjectionULift U = CompleteLocalAlgCat.identityProjection R := sorry

/-- The based functor induced by the inverse of an actual prorepresentation. -/
def prorepresentationFunctor (U : ArtinianLocalAlgCat Λ k ⥤ Type u)
    {R : CompleteLocalAlgCat Λ k} (e : U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) :
    BasedCategory.ofFunctor (CompleteLocalAlgCat.identityProjection R) ⥤ᵇ
      BasedCategory.ofFunctor (elementsProjectionULift U) :=
  BasedFunctor.ofFunctor (ULiftHom.down ⋙ CategoryOfElements.map e.inv ⋙ ULiftHom.up)
    (prorepresentationFunctor_over U e)

/-- Evaluation of a presentation on a prorepresenting identity stage lies over that truncation. -/
theorem fromProrepresentation_over_obj (p : F ⥤ ArtinianLocalAlgCat Λ k)
    (U : ArtinianLocalAlgCat Λ k ⥤ Type u)
    (q : BasedCategory.ofFunctor (elementsProjectionULift U) ⥤ᵇ BasedCategory.ofFunctor p)
    {R : CompleteLocalAlgCat Λ k} (e : U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) (n : ℕ) :
    p.obj (q.obj ((prorepresentationFunctor U e).obj (CompleteLocalAlgCat.identityStage R n))) =
      R.truncation n := sorry

/-- Evaluation of a presentation on prorepresenting successor maps lifts the truncation projection. -/
theorem fromProrepresentation_over_step (p : F ⥤ ArtinianLocalAlgCat Λ k)
    (U : ArtinianLocalAlgCat Λ k ⥤ Type u)
    (q : BasedCategory.ofFunctor (elementsProjectionULift U) ⥤ᵇ BasedCategory.ofFunctor p)
    {R : CompleteLocalAlgCat Λ k} (e : U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) (n : ℕ) :
    p.IsHomLift (R.truncationMap n)
      (q.map ((prorepresentationFunctor U e).map (CompleteLocalAlgCat.identityStageMap R n))) := sorry

/-- Evaluate an actual prorepresentation and a presentation on the canonical identity tower. -/
def fromProrepresentation (p : F ⥤ ArtinianLocalAlgCat Λ k)
    (U : ArtinianLocalAlgCat Λ k ⥤ Type u)
    (q : BasedCategory.ofFunctor (elementsProjectionULift U) ⥤ᵇ BasedCategory.ofFunctor p)
    {R : CompleteLocalAlgCat Λ k} (e : U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) :
    FormalObject p :=
  FormalObject.of R
    (fun n ↦ q.obj ((prorepresentationFunctor U e).obj (CompleteLocalAlgCat.identityStage R n)))
    (fun n ↦ q.map ((prorepresentationFunctor U e).map (CompleteLocalAlgCat.identityStageMap R n)))
    (fromProrepresentation_over_obj p U q e) (fromProrepresentation_over_step p U q e)

/-- A prorepresentation evaluates to a formal object with its actual representing base. -/
theorem fromProrepresentation_base (p : F ⥤ ArtinianLocalAlgCat Λ k)
    (U : ArtinianLocalAlgCat Λ k ⥤ Type u)
    (q : BasedCategory.ofFunctor (elementsProjectionULift U) ⥤ᵇ BasedCategory.ofFunctor p)
    {R : CompleteLocalAlgCat Λ k} (e : U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) :
    (fromProrepresentation p U q e).base = R := rfl

/-- A presentation is minimal when an actual prorepresentation evaluates to a minimal versal object. -/
class IsMinimalPresentation (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] (U : ArtinianLocalAlgCat Λ k ⥤ Type u)
    (q : BasedCategory.ofFunctor (elementsProjectionULift U) ⥤ᵇ BasedCategory.ofFunctor p) : Prop where
  /-- A representing complete local algebra gives a minimal versal formal object for the presentation. -/
  exists_minimal_prorepresentation :
    ∃ (R : CompleteLocalAlgCat Λ k) (e : U ≅ CompleteLocalAlgCat.restrictedCoyoneda R),
      IsMinimalVersal (fromProrepresentation p U q e)

/-- Minimality of a presentation supplies an actual minimal versal prorepresentation. -/
theorem IsMinimalPresentation.spec (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] (U : ArtinianLocalAlgCat Λ k ⥤ Type u)
    (q : BasedCategory.ofFunctor (elementsProjectionULift U) ⥤ᵇ BasedCategory.ofFunctor p)
    [minimal : IsMinimalPresentation p U q] :
    ∃ (R : CompleteLocalAlgCat Λ k) (e : U ≅ CompleteLocalAlgCat.restrictedCoyoneda R),
      IsMinimalVersal (fromProrepresentation p U q e) := minimal.exists_minimal_prorepresentation

end FormalObject

namespace CompleteLocalAlgCat

/-- The identity based functor represents the canonical identity formal object. -/
theorem identityFormalObject_represents (R : CompleteLocalAlgCat Λ k) :
    FormalObject.Represents (identityFormalObject R)
      (BasedFunctor.id (BasedCategory.ofFunctor (identityProjection R))) := sorry

/-- The canonical identity formal object is versal. -/
instance instIsVersalIdentityFormalObject (R : CompleteLocalAlgCat Λ k) :
    FormalObject.IsVersal (identityFormalObject R) := sorry

/-- The canonical identity formal object is minimal versal. -/
instance instIsMinimalVersalIdentityFormalObject (R : CompleteLocalAlgCat Λ k) :
    FormalObject.IsMinimalVersal (identityFormalObject R) := sorry

end CompleteLocalAlgCat

namespace FormalObject

/-- The identity presentation of a restricted coyoneda is a minimal presentation. -/
instance instIsMinimalPresentationIdentity (R : CompleteLocalAlgCat Λ k) :
    IsMinimalPresentation (CompleteLocalAlgCat.identityProjection R)
      (CompleteLocalAlgCat.restrictedCoyoneda R)
      (BasedFunctor.id (BasedCategory.ofFunctor (CompleteLocalAlgCat.identityProjection R))) := sorry

end FormalObject

end
