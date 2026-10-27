/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.AdjointFactorization.Basic

/-!
# Endpoint projections for adjoint factorization

The intermediate vertical-comma category has canonical source and target legs.
This leaf owns their fibredness and objectwise computation rules.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory
open scoped Bicategory

universe u v w

namespace CategoryTheory.FiberedCategoryOver

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, w, w} C}

noncomputable section

namespace AdjointFactorization

/-- The right endpoint projection `VerticalComma F ⥤ X.total`. -/
private def toSourceFunctor (F : X ⟶ Y) : VerticalComma F ⥤ X.total :=
  (verticalArrowProperty F).ι ⋙ Comma.snd _ _

set_option backward.isDefEq.respectTransparency false in
/-- The right endpoint projection is a functor over `C`. -/
private theorem toSourceFunctorComm (F : X ⟶ Y) :
    toSourceFunctor F ⋙ X.p = projection F := by
  rw [← comm F]
  have h (P : VerticalComma F) :
      Y.p.obj ((toFunctor F).obj P.obj.right) = Y.p.obj P.obj.left := by
    letI : Y.p.IsHomLift (𝟙 (Y.p.obj P.obj.left)) P.obj.hom := P.property
    exact IsHomLift.codomain_eq Y.p (𝟙 (Y.p.obj P.obj.left)) P.obj.hom
  refine Functor.ext h ?_
  intro P Q φ
  change Y.p.map ((toFunctor F).map φ.hom.right) =
    eqToHom (h P) ≫ Y.p.map φ.hom.left ≫ eqToHom (h Q).symm
  letI : Y.p.IsHomLift (𝟙 (Y.p.obj P.obj.left)) P.obj.hom := P.property
  letI : Y.p.IsHomLift (𝟙 (Y.p.obj Q.obj.left)) Q.obj.hom := Q.property
  have hp : Y.p.map P.obj.hom = eqToHom (h P).symm := by
    simpa using IsHomLift.fac' Y.p (𝟙 (Y.p.obj P.obj.left)) P.obj.hom
  have hq : Y.p.map Q.obj.hom = eqToHom (h Q).symm := by
    simpa using IsHomLift.fac' Y.p (𝟙 (Y.p.obj Q.obj.left)) Q.obj.hom
  have square := congrArg Y.p.map φ.hom.w
  change Y.p.map (φ.hom.left ≫ Q.obj.hom) =
    Y.p.map (P.obj.hom ≫ (toFunctor F).map φ.hom.right) at square
  rw [Y.p.map_comp, Y.p.map_comp, hp, hq] at square
  calc
    _ = eqToHom (h P) ≫ (eqToHom (h P).symm ≫
        Y.p.map ((toFunctor F).map φ.hom.right)) := by simp
    _ = _ := congrArg (fun k => eqToHom (h P) ≫ k) square.symm

/-- The left endpoint projection `VerticalComma F ⥤ Y.total`. -/
private def toTargetFunctor (F : X ⟶ Y) : VerticalComma F ⥤ Y.total :=
  (verticalArrowProperty F).ι ⋙ Comma.fst _ _

/-- The left endpoint projection is a functor over `C`. -/
private theorem toTargetFunctorComm (F : X ⟶ Y) :
    toTargetFunctor F ⋙ Y.p = projection F := rfl

private theorem target_isHomLift_iff (F : X ⟶ Y) {P Q : VerticalComma F}
    {U V : C} (f : U ⟶ V) (φ : P ⟶ Q) :
    (projection F).IsHomLift f φ ↔ Y.p.IsHomLift f φ.hom.left := by
  constructor
  · intro hφ
    cases hφ
    exact .map _
  · intro hφ
    cases hφ
    exact .map _

private theorem source_isHomLift (F : X ⟶ Y) {P Q : VerticalComma F}
    {U V : C} (f : U ⟶ V) (φ : P ⟶ Q)
    (hφ : (projection F).IsHomLift f φ) : X.p.IsHomLift f φ.hom.right := by
  let G : (middle F).toBasedCategory ⥤ᵇ X.toBasedCategory :=
    { toFunctor := toSourceFunctor F, w := toSourceFunctorComm F }
  exact @BasedFunctor.preserves_isHomLift C _ _ _ G _ _ _ _ f φ hφ

private theorem stronglyCartesian_over_map {S : Type*} [Category* S] (p : S ⥤ C)
    {U V : C} (f : U ⟶ V) {a b : S} (φ : a ⟶ b)
    (hφ : p.IsStronglyCartesian f φ) : p.IsStronglyCartesian (p.map φ) φ := by
  cases hφ.toIsHomLift
  exact hφ

set_option backward.isDefEq.respectTransparency false in
/-- A comma square with strongly cartesian endpoint maps is strongly cartesian over the base. -/
private theorem stronglyCartesian_of_components (F : X ⟶ Y)
    {P Q : VerticalComma F} {U V : C} (f : U ⟶ V) (φ : P ⟶ Q)
    (hl : Y.p.IsStronglyCartesian f φ.hom.left)
    (hr : X.p.IsStronglyCartesian f φ.hom.right) :
    (projection F).IsStronglyCartesian f φ := by
  letI := hl
  letI := hr
  haveI hF : Y.p.IsStronglyCartesian f ((toFunctor F).map φ.hom.right) :=
    CartesianBasedFunctor.Map.stronglyCartesianOfLift (toCartesianBasedFunctor F) f _ hr
  refine { toIsHomLift := (target_isHomLift_iff F f φ).2 hl.toIsHomLift, universal_property' := ?_ }
  intro R g χ hχ
  haveI : Y.p.IsHomLift (g ≫ f) χ.hom.left :=
    (target_isHomLift_iff F (g ≫ f) χ).1 hχ
  haveI := source_isHomLift F (g ≫ f) χ hχ
  obtain ⟨a, ⟨ha, hfac_a⟩, huniq_a⟩ :=
    Functor.IsStronglyCartesian.universal_property X.p f φ.hom.right g (g ≫ f) rfl χ.hom.right
  obtain ⟨b, ⟨hb, hfac_b⟩, huniq_b⟩ :=
    Functor.IsStronglyCartesian.universal_property Y.p f φ.hom.left g (g ≫ f) rfl χ.hom.left
  letI := ha
  letI := hb
  letI : Y.p.IsHomLift (𝟙 (Y.p.obj P.obj.left)) P.obj.hom := P.property
  letI : Y.p.IsHomLift (𝟙 (Y.p.obj R.obj.left)) R.obj.hom := R.property
  haveI : Y.p.IsHomLift g ((toFunctor F).map a) :=
    BasedFunctor.preserves_isHomLift (toBasedFunctor F) g a
  haveI : Y.p.IsHomLift g (b ≫ P.obj.hom) :=
    IsHomLift.comp_lift_id_right' Y.p g b (Y.p.obj P.obj.left) P.obj.hom
  haveI : Y.p.IsHomLift g (R.obj.hom ≫ (toFunctor F).map a) :=
    IsHomLift.comp_lift_id_left' Y.p (Y.p.obj R.obj.left) R.obj.hom g ((toFunctor F).map a)
  have square : b ≫ P.obj.hom = R.obj.hom ≫ (toFunctor F).map a := by
    apply Functor.IsStronglyCartesian.ext Y.p f ((toFunctor F).map φ.hom.right) g
    calc
      (b ≫ P.obj.hom) ≫ (toFunctor F).map φ.hom.right =
          b ≫ (φ.hom.left ≫ Q.obj.hom) := by rw [Category.assoc, ← φ.hom.w, Functor.id_map]
      _ = χ.hom.left ≫ Q.obj.hom := by rw [← Category.assoc, hfac_b]
      _ = R.obj.hom ≫ (toFunctor F).map χ.hom.right := χ.hom.w
      _ = (R.obj.hom ≫ (toFunctor F).map a) ≫ (toFunctor F).map φ.hom.right := by
        rw [Category.assoc, ← Functor.map_comp, hfac_a]
  let τ : R ⟶ P := ObjectProperty.homMk { left := b, right := a, w := square }
  refine ⟨τ, ⟨(target_isHomLift_iff F g τ).2 hb, ?_⟩, ?_⟩
  · apply ObjectProperty.hom_ext
    exact Comma.hom_ext _ _ hfac_b hfac_a
  · intro τ' ⟨hτ', hfac⟩
    haveI : Y.p.IsHomLift g τ'.hom.left := (target_isHomLift_iff F g τ').1 hτ'
    haveI := source_isHomLift F g τ' hτ'
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · exact huniq_b _ ⟨inferInstance, congrArg (fun η => η.hom.left) hfac⟩
    · exact huniq_a _ ⟨inferInstance, congrArg (fun η => η.hom.right) hfac⟩

set_option backward.isDefEq.respectTransparency false in
/-- Pull both endpoints back and lift the comparison through the image of the source lift. -/
private theorem exists_cartesian_components (F : X ⟶ Y) (Q : VerticalComma F)
    (U : C) (f : U ⟶ (projection F).obj Q) :
    ∃ (P : VerticalComma F) (φ : P ⟶ Q),
      Y.p.IsStronglyCartesian f φ.hom.left ∧ X.p.IsStronglyCartesian f φ.hom.right := by
  obtain ⟨x, a, ha⟩ := IsPreFibered.exists_isCartesian X.p (a := Q.obj.right)
    (Functor.congr_obj (toSourceFunctorComm F) Q) f
  obtain ⟨y, b, hb⟩ := IsPreFibered.exists_isCartesian Y.p (a := Q.obj.left) rfl f
  letI := ha
  letI := hb
  haveI ha' : X.p.IsStronglyCartesian f a := inferInstance
  haveI hb' : Y.p.IsStronglyCartesian f b := inferInstance
  haveI : Y.p.IsStronglyCartesian f ((toFunctor F).map a) :=
    CartesianBasedFunctor.Map.stronglyCartesianOfLift (toCartesianBasedFunctor F) f a ha'
  letI : Y.p.IsHomLift (𝟙 (Y.p.obj Q.obj.left)) Q.obj.hom := Q.property
  haveI : Y.p.IsHomLift f (b ≫ Q.obj.hom) :=
    IsHomLift.comp_lift_id_right' Y.p f b (Y.p.obj Q.obj.left) Q.obj.hom
  obtain ⟨c, ⟨hc, hfac⟩, _⟩ :=
    Functor.IsStronglyCartesian.universal_property Y.p f ((toFunctor F).map a)
      (𝟙 U) f (by simp) (b ≫ Q.obj.hom)
  have hy : Y.p.obj y = U := IsHomLift.domain_eq Y.p f b
  have hc' : Y.p.IsHomLift (𝟙 (Y.p.obj y)) c := by
    rw [hy]
    exact hc
  let P : VerticalComma F := ⟨{ left := y, right := x, hom := c }, hc'⟩
  let φ : P ⟶ Q := ObjectProperty.homMk { left := b, right := a, w := hfac.symm }
  exact ⟨P, φ, hb', ha'⟩

/-- The right endpoint projection preserves strongly cartesian arrows. -/
private theorem toSourcePreservesStronglyCartesian (F : X ⟶ Y) :
    BasedFunctor.PreservesStronglyCartesian
      ({ toFunctor := toSourceFunctor F
         w := toSourceFunctorComm F } :
        (middle F).toBasedCategory ⥤ᵇ X.toBasedCategory) := by
  intro P Q φ hφ
  letI : (projection F).IsStronglyCartesian ((projection F).map φ) φ := hφ
  obtain ⟨R, ψ, hl, hr⟩ :=
    exists_cartesian_components F Q ((projection F).obj P) ((projection F).map φ)
  haveI := stronglyCartesian_of_components F ((projection F).map φ) ψ hl hr
  let e := Functor.IsCartesian.domainUniqueUpToIso (projection F) ((projection F).map φ) ψ φ
  have heq : e.hom.hom.right ≫ ψ.hom.right = φ.hom.right :=
    congrArg (fun η => η.hom.right)
      (Functor.IsCartesian.fac (projection F) ((projection F).map φ) ψ φ)
  haveI : X.p.IsStronglyCartesian (X.p.map ψ.hom.right) ψ.hom.right :=
    stronglyCartesian_over_map X.p _ _ hr
  haveI : IsIso e.hom.hom.right := (toSourceFunctor F).map_isIso e.hom
  have hcomp : X.p.IsStronglyCartesian
      (X.p.map (e.hom.hom.right ≫ ψ.hom.right)) (e.hom.hom.right ≫ ψ.hom.right) := by
    simpa only [Functor.map_comp] using
      (inferInstance : X.p.IsStronglyCartesian
        (X.p.map e.hom.hom.right ≫ X.p.map ψ.hom.right) (e.hom.hom.right ≫ ψ.hom.right))
  change X.p.IsStronglyCartesian (X.p.map φ.hom.right) φ.hom.right
  simpa only [heq] using hcomp

/-- The projection from the intermediate fibred category back to `X`. -/
def toSource (F : X ⟶ Y) : middle F ⟶ X :=
  ofBasedFunctor
    ({ toFunctor := toSourceFunctor F
       w := toSourceFunctorComm F } :
      (middle F).toBasedCategory ⥤ᵇ X.toBasedCategory)
    (toSourcePreservesStronglyCartesian F)

/-- `toSource F` sends a vertical arrow to its source-side endpoint. -/
@[simp]
theorem toSource_obj (F : X ⟶ Y) (P : VerticalComma F) :
    (toFunctor (toSource F)).obj P = P.obj.right := rfl

/-- `toSource F` sends a vertical comma square to its source-side component. -/
@[simp]
theorem toSource_map (F : X ⟶ Y) {P Q : VerticalComma F} (φ : P ⟶ Q) :
    (toFunctor (toSource F)).map φ = φ.hom.right := rfl

/-- The left endpoint projection preserves strongly cartesian arrows. -/
private theorem toTargetPreservesStronglyCartesian (F : X ⟶ Y) :
    BasedFunctor.PreservesStronglyCartesian
      ({ toFunctor := toTargetFunctor F
         w := toTargetFunctorComm F } :
        (middle F).toBasedCategory ⥤ᵇ Y.toBasedCategory) := by
  intro P Q φ hφ
  letI : (projection F).IsStronglyCartesian ((projection F).map φ) φ := hφ
  obtain ⟨R, ψ, hl, hr⟩ :=
    exists_cartesian_components F Q ((projection F).obj P) ((projection F).map φ)
  haveI := stronglyCartesian_of_components F ((projection F).map φ) ψ hl hr
  let e := Functor.IsCartesian.domainUniqueUpToIso (projection F) ((projection F).map φ) ψ φ
  have heq : e.hom.hom.left ≫ ψ.hom.left = φ.hom.left :=
    congrArg (fun η => η.hom.left)
      (Functor.IsCartesian.fac (projection F) ((projection F).map φ) ψ φ)
  haveI : Y.p.IsStronglyCartesian (Y.p.map ψ.hom.left) ψ.hom.left :=
    stronglyCartesian_over_map Y.p _ _ hl
  haveI : IsIso e.hom.hom.left := (toTargetFunctor F).map_isIso e.hom
  have hcomp : Y.p.IsStronglyCartesian
      (Y.p.map (e.hom.hom.left ≫ ψ.hom.left)) (e.hom.hom.left ≫ ψ.hom.left) := by
    simpa only [Functor.map_comp] using
      (inferInstance : Y.p.IsStronglyCartesian
        (Y.p.map e.hom.hom.left ≫ Y.p.map ψ.hom.left) (e.hom.hom.left ≫ ψ.hom.left))
  change Y.p.IsStronglyCartesian (Y.p.map φ.hom.left) φ.hom.left
  simpa only [heq] using hcomp

/-- The projection from the intermediate fibred category to `Y`. -/
def toTarget (F : X ⟶ Y) : middle F ⟶ Y :=
  ofBasedFunctor
    ({ toFunctor := toTargetFunctor F
       w := toTargetFunctorComm F } :
      (middle F).toBasedCategory ⥤ᵇ Y.toBasedCategory)
    (toTargetPreservesStronglyCartesian F)

/-- `toTarget F` sends a vertical arrow to its target-side endpoint. -/
@[simp]
theorem toTarget_obj (F : X ⟶ Y) (P : VerticalComma F) :
    (toFunctor (toTarget F)).obj P = P.obj.left := rfl

/-- `toTarget F` sends a vertical comma square to its target-side component. -/
@[simp]
theorem toTarget_map (F : X ⟶ Y) {P Q : VerticalComma F} (φ : P ⟶ Q) :
    (toFunctor (toTarget F)).map φ = φ.hom.left := rfl

set_option backward.isDefEq.respectTransparency false in
/-- A square whose source component is strongly cartesian is strongly cartesian over its target. -/
private theorem stronglyCartesian_toTarget_of_source (F : X ⟶ Y)
    {P Q : VerticalComma F} (φ : P ⟶ Q)
    (hr : X.p.IsStronglyCartesian (Y.p.map φ.hom.left) φ.hom.right) :
    (toTargetFunctor F).IsStronglyCartesian φ.hom.left φ := by
  letI := hr
  haveI : Y.p.IsStronglyCartesian (Y.p.map φ.hom.left)
      ((toFunctor F).map φ.hom.right) :=
    CartesianBasedFunctor.Map.stronglyCartesianOfLift (toCartesianBasedFunctor F) _ _ hr
  refine { toIsHomLift := .map φ, universal_property' := ?_ }
  intro R g χ hχ
  letI : (toTargetFunctor F).IsHomLift (g ≫ φ.hom.left) χ := hχ
  have hχleft : χ.hom.left = g ≫ φ.hom.left :=
    (IsHomLift.eq_of_isHomLift (toTargetFunctor F) (g ≫ φ.hom.left) χ).symm
  have hχbase : (projection F).IsHomLift (Y.p.map g ≫ Y.p.map φ.hom.left) χ := by
    have : (projection F).IsHomLift (Y.p.map χ.hom.left) χ := .map χ
    simpa only [hχleft, Functor.map_comp] using this
  haveI := source_isHomLift F _ χ hχbase
  obtain ⟨a, ⟨ha, hfac_a⟩, huniq_a⟩ :=
    Functor.IsStronglyCartesian.universal_property X.p (Y.p.map φ.hom.left) φ.hom.right
      (Y.p.map g) (Y.p.map g ≫ Y.p.map φ.hom.left) rfl χ.hom.right
  letI := ha
  letI : Y.p.IsHomLift (𝟙 (Y.p.obj P.obj.left)) P.obj.hom := P.property
  letI : Y.p.IsHomLift (𝟙 (Y.p.obj R.obj.left)) R.obj.hom := R.property
  haveI : Y.p.IsHomLift (Y.p.map g) ((toFunctor F).map a) :=
    BasedFunctor.preserves_isHomLift (toBasedFunctor F) _ a
  haveI : Y.p.IsHomLift (Y.p.map g) (R.obj.hom ≫ (toFunctor F).map a) :=
    IsHomLift.comp_lift_id_left' Y.p (Y.p.obj R.obj.left) R.obj.hom _ ((toFunctor F).map a)
  have square : g ≫ P.obj.hom = R.obj.hom ≫ (toFunctor F).map a := by
    apply Functor.IsStronglyCartesian.ext Y.p (Y.p.map φ.hom.left)
      ((toFunctor F).map φ.hom.right) (Y.p.map g)
    calc
      (g ≫ P.obj.hom) ≫ (toFunctor F).map φ.hom.right =
          g ≫ (φ.hom.left ≫ Q.obj.hom) := by rw [Category.assoc, ← φ.hom.w, Functor.id_map]
      _ = χ.hom.left ≫ Q.obj.hom := by rw [← Category.assoc, ← hχleft]
      _ = R.obj.hom ≫ (toFunctor F).map χ.hom.right := χ.hom.w
      _ = (R.obj.hom ≫ (toFunctor F).map a) ≫ (toFunctor F).map φ.hom.right := by
        rw [Category.assoc, ← Functor.map_comp, hfac_a]
  let τ : R ⟶ P := ObjectProperty.homMk { left := g, right := a, w := square }
  refine ⟨τ, ⟨.map τ, ?_⟩, ?_⟩
  · apply ObjectProperty.hom_ext
    exact Comma.hom_ext _ _ hχleft.symm hfac_a
  · intro τ' ⟨hτ', hfac⟩
    letI : (toTargetFunctor F).IsHomLift g τ' := hτ'
    have hleft : τ'.hom.left = g :=
      (IsHomLift.eq_of_isHomLift (toTargetFunctor F) g τ').symm
    have hbase : (projection F).IsHomLift (Y.p.map g) τ' := by
      have : (projection F).IsHomLift (Y.p.map τ'.hom.left) τ' := .map τ'
      simpa only [hleft] using this
    haveI := source_isHomLift F _ τ' hbase
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · exact hleft
    · exact huniq_a _ ⟨inferInstance, congrArg (fun η => η.hom.right) hfac⟩

set_option backward.isDefEq.respectTransparency false in
/-- The target leg of the canonical factorization is a fibred functor. -/
@[instance]
theorem toTargetIsFibered (F : X ⟶ Y) :
    (toFunctor (toTarget F)).IsFibered := by
  change (toTargetFunctor F).IsFibered
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro Q y b
  obtain ⟨x, a, ha⟩ := IsPreFibered.exists_isCartesian X.p (a := Q.obj.right)
    (Functor.congr_obj (toSourceFunctorComm F) Q) (Y.p.map b)
  letI := ha
  haveI ha' : X.p.IsStronglyCartesian (Y.p.map b) a := inferInstance
  haveI : Y.p.IsStronglyCartesian (Y.p.map b) ((toFunctor F).map a) :=
    CartesianBasedFunctor.Map.stronglyCartesianOfLift (toCartesianBasedFunctor F) _ _ ha'
  letI : Y.p.IsHomLift (𝟙 (Y.p.obj Q.obj.left)) Q.obj.hom := Q.property
  haveI : Y.p.IsHomLift (Y.p.map b) (b ≫ Q.obj.hom) :=
    IsHomLift.comp_lift_id_right' Y.p (Y.p.map b) b (Y.p.obj Q.obj.left) Q.obj.hom
  obtain ⟨c, ⟨hc, hfac⟩, _⟩ :=
    Functor.IsStronglyCartesian.universal_property Y.p (Y.p.map b) ((toFunctor F).map a)
      (𝟙 (Y.p.obj y)) (Y.p.map b) (by simp) (b ≫ Q.obj.hom)
  let P : VerticalComma F := ⟨{ left := y, right := x, hom := c }, hc⟩
  let φ : P ⟶ Q := ObjectProperty.homMk { left := b, right := a, w := hfac.symm }
  exact ⟨P, φ, stronglyCartesian_toTarget_of_source F φ ha'⟩

end AdjointFactorization

end

end CategoryTheory.FiberedCategoryOver
