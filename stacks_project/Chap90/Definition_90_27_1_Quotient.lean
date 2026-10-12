/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Grothendieck
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import stacks_project.Chap90.Definition_90_21_1_Groupoid
public import stacks_project.Chap90.Definition_90_27_1_MinimalVersal
public import stacks_project.Chap90.Remarks_90_5_2_Grothendieck

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

universe u v w

namespace CategoryTheory.GroupoidInFunctors

section QuotientGeneral

variable {C : Type u} [Category.{v} C]

/-- The category-valued functor sending `T` to the fibre groupoid of `G` at `T`. -/
def toCatFunctor (G : GroupoidInFunctors C) : C ⥤ Cat.{w, w} :=
  G.toFunctor ⋙ Grpd.forgetToCat

/-- `toCatFunctor` is `toFunctor` composed with `Grpd.forgetToCat`. -/
theorem toCatFunctor_eq (G : GroupoidInFunctors C) :
    G.toCatFunctor = G.toFunctor ⋙ Grpd.forgetToCat :=
  rfl

/-- On objects, `toCatFunctor` is the fibre groupoid viewed as a category. -/
theorem toCatFunctor_obj (G : GroupoidInFunctors C) (T : C) :
    G.toCatFunctor.obj T = Grpd.forgetToCat.obj (G.toFunctor.obj T) :=
  rfl

/-- The quotient category `[U/R]` associated to a groupoid in functors. -/
abbrev quotient (G : GroupoidInFunctors C) :=
  Grothendieck G.toCatFunctor

/-- The quotient is the Grothendieck construction of `toCatFunctor`. -/
theorem quotient_eq (G : GroupoidInFunctors C) :
    G.quotient = Grothendieck G.toCatFunctor :=
  sorry

/-- The projection `[U/R] ⟶ C`. -/
def forget (G : GroupoidInFunctors C) : G.quotient ⥤ C :=
  Grothendieck.forget G.toCatFunctor

/-- The projection of the quotient is the Grothendieck forgetful functor. -/
theorem forget_eq (G : GroupoidInFunctors C) :
    G.forget = Grothendieck.forget G.toCatFunctor :=
  rfl

/-- The Grothendieck object `(T, x)` associated to an element of `U(T)`. -/
def quotientObj (G : GroupoidInFunctors C) (T : C) (x : G.U.obj T) : G.quotient :=
  ⟨T, x⟩

/-- The projection of `(T, x)` is `T`. -/
theorem forget_obj (G : GroupoidInFunctors C) (T : C) (x : G.U.obj T) :
    G.forget.obj (G.quotientObj T x) = T :=
  rfl

/-- The underlying functor of the quotient morphism `U ⟶ [U/R]`. -/
def quotientMorphismFunctor (G : GroupoidInFunctors C) :
    G.U.Elements ⥤ G.quotient where
  obj p := G.quotientObj p.1 p.2
  map {p q} f :=
    { base := f.val
      fiber := eqToHom sorry }
  map_id := sorry
  map_comp := sorry

/-- On objects, `quotientMorphismFunctor` sends `⟨T, x⟩` to `(T, x)`. -/
theorem quotientMorphismFunctor_obj (G : GroupoidInFunctors C) (T : C)
    (x : G.U.obj T) :
    (quotientMorphismFunctor G).obj ⟨T, x⟩ = G.quotientObj T x :=
  sorry

/-- The quotient morphism `U ⟶ [U/R]` as a based functor over `C`. -/
def quotientMorphism (G : GroupoidInFunctors C) :
    BasedCategory.ofFunctor (CategoryOfElements.π G.U) ⥤ᵇ
      BasedCategory.ofFunctor G.forget :=
  BasedFunctor.ofFunctor G.quotientMorphismFunctor sorry

/-- On objects, the quotient morphism sends `x ∈ U(T)` to `(T, x)`. -/
theorem quotientMorphism_obj (G : GroupoidInFunctors C) (T : C) (x : G.U.obj T) :
    (quotientMorphism G).obj ⟨T, x⟩ = G.quotientObj T x :=
  rfl

/-- The quotient morphism lies over `C`. -/
theorem quotientMorphism_comp_forget (G : GroupoidInFunctors C) :
    (quotientMorphism G).toFunctor ⋙ G.forget = CategoryOfElements.π G.U :=
  sorry

end QuotientGeneral

section QuotientFormal

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))

/-- Hom-universe lift of `[U/R]`, matching the universe constraint of `FormalObject`. -/
abbrev quotientTotal : Type (u + 1) :=
  ULiftHom.{u + 1} G.quotient

/-- `quotientTotal` is the Hom-universe lift of `[U/R]`. -/
theorem quotientTotal_eq : G.quotientTotal = ULiftHom.{u + 1} G.quotient :=
  sorry

/-- Projection of the Hom-universe lift of `[U/R]` to `C_Λ`. -/
def forgetULift : G.quotientTotal ⥤ ArtinianLocalAlgCat Λ k :=
  (ULiftHom.down : G.quotientTotal ⥤ G.quotient) ⋙ G.forget

/-- `forgetULift` is the Grothendieck projection after Hom-universe forgetful. -/
theorem forgetULift_eq :
    G.forgetULift = (ULiftHom.down : G.quotientTotal ⥤ G.quotient) ⋙ G.forget :=
  sorry

/-- The lifted quotient projection is cofibered in groupoids. -/
instance forgetULift_op_inGroupoids :
    Functor.IsFibered.InGroupoids G.forgetULift.op :=
  sorry

/-- Stage `n` of the formal object associated to a prorepresentation of `U`, as an
object of `[U/R]`. -/
noncomputable def quotientStage {R : CompleteLocalAlgCat Λ k}
    (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) (n : ℕ) : G.quotient :=
  G.quotientObj (R.truncation n) (e.inv.app (R.truncation n) (R.truncationToInclusion n))

/-- The projection of `quotientStage e n` is the `n`th truncation of `R`. -/
theorem quotientStage_forget {R : CompleteLocalAlgCat Λ k}
    (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) (n : ℕ) :
    G.forget.obj (G.quotientStage e n) = R.truncation n :=
  sorry

/-- The successor transition of `quotientStage` in `[U/R]`. -/
def quotientStageMap {R : CompleteLocalAlgCat Λ k}
    (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) (n : ℕ) :
    G.quotientStage e (n + 1) ⟶ G.quotientStage e n where
  base := R.truncationMap n
  fiber := eqToHom sorry

/-- The base of `quotientStageMap e n` is the truncation projection of `R`. -/
theorem quotientStageMap_base {R : CompleteLocalAlgCat Λ k}
    (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) (n : ℕ) :
    (G.quotientStageMap e n).base = R.truncationMap n :=
  sorry

/-- Stage `n` of `quotientFormalObject` in the Hom-universe lift of `[U/R]`. -/
def quotientStageULift {R : CompleteLocalAlgCat Λ k}
    (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) (n : ℕ) : G.quotientTotal :=
  ULiftHom.objUp (G.quotientStage e n)

/-- `quotientStageULift e n` is the Hom-universe lift of `quotientStage e n`. -/
theorem quotientStageULift_eq {R : CompleteLocalAlgCat Λ k}
    (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) (n : ℕ) :
    G.quotientStageULift e n = ULiftHom.objUp (G.quotientStage e n) :=
  sorry

/-- Successor transition of lifted quotient stages. -/
def quotientStageULiftMap {R : CompleteLocalAlgCat Λ k}
    (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) (n : ℕ) :
    G.quotientStageULift e (n + 1) ⟶ G.quotientStageULift e n :=
  (ULiftHom.up : G.quotient ⥤ G.quotientTotal).map (G.quotientStageMap e n)

/-- `quotientStageULiftMap` is the image of `quotientStageMap` under `ULiftHom.up`. -/
theorem quotientStageULiftMap_eq {R : CompleteLocalAlgCat Λ k}
    (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) (n : ℕ) :
    G.quotientStageULiftMap e n =
      (ULiftHom.up : G.quotient ⥤ G.quotientTotal).map (G.quotientStageMap e n) :=
  sorry

/-- The formal object of `[U/R]` associated to a prorepresentation `e : U ≅ restrictedCoyoneda R`,
given by the images of the identity truncations of `R` under the quotient morphism. -/
def quotientFormalObject {R : CompleteLocalAlgCat Λ k}
    (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) :
    FormalObject G.forgetULift where
  base := R
  system := Functor.ofOpSequence (G.quotientStageULiftMap e)
  over_obj := sorry
  over_step := sorry

/-- The complete local base of `quotientFormalObject e` is the prorepresenting algebra. -/
theorem quotientFormalObject_base {R : CompleteLocalAlgCat Λ k}
    (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) :
    (G.quotientFormalObject e).base = R :=
  sorry

/-- Stage `n` of `quotientFormalObject e` lies over the `n`th truncation of `R`. -/
theorem quotientFormalObject_spec {R : CompleteLocalAlgCat Λ k}
    (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R) (n : ℕ) :
    G.forgetULift.obj ((G.quotientFormalObject e).system.family n) = R.truncation n ∧
      G.forgetULift.IsHomLift (R.truncationMap n)
        ((G.quotientFormalObject e).system.stepMap n) :=
  sorry

end QuotientFormal

end CategoryTheory.GroupoidInFunctors

end QuotientData
