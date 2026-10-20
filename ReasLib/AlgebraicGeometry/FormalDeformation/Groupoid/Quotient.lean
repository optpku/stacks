module

public import ReasLib.CategoryTheory.Groupoid.Quotient
public import ReasLib.CategoryTheory.Cofibered.ULiftHom
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Versal

/-!
# Quotient of a groupoid in functors

The assignment `T ↦ (U(T), R(T), s, t, c)` determines a functor `C ⥤ Grpd`. The
quotient `[U/R]` is the Grothendieck construction of the associated category-valued
functor, and the quotient morphism `U ⟶ [U/R]` sends `x ∈ U(T)` to the object
`(T, x)`.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

noncomputable section QuotientData

universe u v w lift

namespace CategoryTheory.Functor

/-- The projection from the Hom-universe lift of a groupoid-valued functor's Grothendieck construction. -/
def groupoidCopresheafProjectionULift {C : Type u} [Category.{v} C]
    (F : C ⥤ Grpd.{w, w}) :
    ULiftHom.{lift} (Grothendieck (F ⋙ Grpd.forgetToCat)) ⥤ C :=
  ULiftHom.down ⋙ Grothendieck.forget (F ⋙ Grpd.forgetToCat)

end CategoryTheory.Functor

namespace CategoryTheory.GroupoidInFunctors

section QuotientGeneral

variable {C : Type u} [Category.{v} C]

/-- The category-valued functor sending `T` to the fibre groupoid of `G` at `T`. -/
abbrev toCatFunctor (G : GroupoidInFunctors C) : C ⥤ Cat.{w, w} :=
  G.toFunctor ⋙ Grpd.forgetToCat

/-- `toCatFunctor` is `toFunctor` composed with `Grpd.forgetToCat`. -/
theorem toCatFunctor_eq (G : GroupoidInFunctors C) :
    G.toCatFunctor = G.toFunctor ⋙ Grpd.forgetToCat :=
  rfl

/-- On objects, `toCatFunctor` is the fibre groupoid viewed as a category. -/
theorem toCatFunctor_obj (G : GroupoidInFunctors C) (T : C) :
    G.toCatFunctor.obj T = Grpd.forgetToCat.obj (G.toFunctor.obj T) :=
  rfl

/-- The projection `[U/R] ⟶ C`. -/
def forget (G : GroupoidInFunctors C) : G.quotient.total ⥤ C :=
  G.quotient.p

/-- The projection of the quotient is the Grothendieck forgetful functor. -/
theorem forget_eq (G : GroupoidInFunctors C) :
    G.forget = Grothendieck.forget G.toCatFunctor :=
  rfl

/-- The projection of `(T, x)` is `T`. -/
theorem forget_obj (G : GroupoidInFunctors C) (T : C) (x : G.U.obj T) :
    G.forget.obj (G.quotientObj T x) = T :=
  rfl

/-- The canonical quotient functor commutes with projection to the base. -/
theorem quotientMorphismFunctor_over (G : GroupoidInFunctors C) :
    G.quotientMorphismFunctor ⋙ G.forget = CategoryOfElements.π G.U :=
  quotientMorphismFunctor_comp_p G

/-- The quotient morphism lies over `C`. -/
theorem quotientMorphism_comp_forget (G : GroupoidInFunctors C) :
    (quotientMorphism G).toFunctor ⋙ G.forget = CategoryOfElements.π G.U :=
  (quotientMorphism G).w

end QuotientGeneral

section QuotientFormal

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))

/-- Hom-universe lift of `[U/R]`, matching the universe constraint of `FormalObject`. -/
abbrev quotientTotal : Type (u + 1) :=
  ULiftHom.{u + 1} G.quotient.total

/-- `quotientTotal` is the Hom-universe lift of `[U/R]`. -/
theorem quotientTotal_eq : G.quotientTotal = ULiftHom.{u + 1} G.quotient.total :=
  rfl

/-- Projection of the lifted quotient to the Artinian base category. -/
abbrev forgetULift : G.quotientTotal ⥤ ArtinianLocalAlgCat Λ k :=
  ULiftHom.down ⋙ G.quotient.p

/-- The lifted quotient projection forgets the lift and then the quotient object. -/
theorem forgetULift_eq :
    G.forgetULift = (ULiftHom.down : G.quotientTotal ⥤ G.quotient.total) ⋙ G.forget := rfl

/-- The quotient presentation as a functor between Hom-universe-lifted categories. -/
def quotientMorphismULift :
    BasedCategory.ofFunctor (FormalObject.elementsProjectionULift G.U) ⥤ᵇ
      BasedCategory.ofFunctor G.forgetULift :=
  BasedFunctor.ofFunctor (ULiftHom.down ⋙ G.quotientMorphismFunctor ⋙ ULiftHom.up) (by
    change ULiftHom.down ⋙ (G.quotientMorphismFunctor ⋙ G.forget) = _
    rw [G.quotientMorphismFunctor_over]
    rfl)

/-- Stage `n` of the formal object associated to a prorepresentation of `U`, as an
object of `[U/R]`. -/
noncomputable def quotientStage {R : CompleteLocalAlgCat Λ k}
    (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) (n : ℕ) : G.quotient.total :=
  G.quotientObj (R.truncation n) (e.inv.app (R.truncation n) ((FormalObject.restrictedIdentity R n).2))

/-- The projection of `quotientStage e n` is the `n`th truncation of `R`. -/
theorem quotientStage_forget {R : CompleteLocalAlgCat Λ k}
    (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) (n : ℕ) :
    G.forget.obj (G.quotientStage e n) = R.truncation n :=
  rfl

/-- Successor quotient stages are the functorial images of canonical identity transitions. -/
noncomputable def quotientStageMap {R : CompleteLocalAlgCat Λ k}
    (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) (n : ℕ) :
    G.quotientStage e (n + 1) ⟶ G.quotientStage e n :=
  G.quotientMorphismFunctor.map
    ((CategoryOfElements.map e.inv).map (FormalObject.restrictedIdentityMap R n))

/-- The base of `quotientStageMap e n` is the truncation projection of `R`. -/
theorem quotientStageMap_base {R : CompleteLocalAlgCat Λ k}
    (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) (n : ℕ) :
    (G.quotientStageMap e n).base = R.truncationMap n :=
  rfl

/-- Stage `n` of `quotientFormalObject` in the Hom-universe lift of `[U/R]`. -/
def quotientStageULift {R : CompleteLocalAlgCat Λ k}
    (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) (n : ℕ) : G.quotientTotal :=
  ULiftHom.objUp (G.quotientStage e n)

/-- `quotientStageULift e n` is the Hom-universe lift of `quotientStage e n`. -/
theorem quotientStageULift_eq {R : CompleteLocalAlgCat Λ k}
    (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) (n : ℕ) :
    G.quotientStageULift e n = ULiftHom.objUp (G.quotientStage e n) :=
  rfl

/-- Successor transition of lifted quotient stages. -/
def quotientStageULiftMap {R : CompleteLocalAlgCat Λ k}
    (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) (n : ℕ) :
    G.quotientStageULift e (n + 1) ⟶ G.quotientStageULift e n :=
  (ULiftHom.up : G.quotient.total ⥤ G.quotientTotal).map (G.quotientStageMap e n)

/-- `quotientStageULiftMap` is the image of `quotientStageMap` under `ULiftHom.up`. -/
theorem quotientStageULiftMap_eq {R : CompleteLocalAlgCat Λ k}
    (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) (n : ℕ) :
    G.quotientStageULiftMap e n =
      (ULiftHom.up : G.quotient.total ⥤ G.quotientTotal).map (G.quotientStageMap e n) :=
  rfl

/-- The quotient formal object evaluates the actual presentation on a prorepresenting identity tower. -/
noncomputable def quotientFormalObject {R : CompleteLocalAlgCat Λ k}
    (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) : FormalObject G.forgetULift :=
  FormalObject.fromProrepresentation G.forgetULift G.U G.quotientMorphismULift e

/-- The complete local base of `quotientFormalObject e` is the prorepresenting algebra. -/
theorem quotientFormalObject_base {R : CompleteLocalAlgCat Λ k}
    (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) :
    (G.quotientFormalObject e).base = R :=
  rfl

/-- Stage `n` of `quotientFormalObject e` lies over the `n`th truncation of `R`. -/
theorem quotientFormalObject_spec {R : CompleteLocalAlgCat Λ k}
    (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) (n : ℕ) :
    G.forgetULift.obj ((G.quotientFormalObject e).system.family n) = R.truncation n ∧
      G.forgetULift.IsHomLift (R.truncationMap n)
        ((G.quotientFormalObject e).system.stepMap n) :=
  ⟨(G.quotientFormalObject e).over_obj n, (G.quotientFormalObject e).over_step n⟩

end QuotientFormal

end CategoryTheory.GroupoidInFunctors

end QuotientData
