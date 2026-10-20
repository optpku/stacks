module

public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Comparison
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Value.Explicit

/-!
# Total Derived Values Computed by Local Replacements

If one endpoint of a local equivalence computes a derived functor, the original functor at that
endpoint is canonically isomorphic to the total derived value at the other endpoint.  This file
packages that ubiquitous replacement step, independently of complexes or a chosen localization
model, and exposes both orientations of each comparison.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {D : Type u₁} {D' : Type u₂} {E : Type u₃}
variable [Category.{v₁} D] [Category.{v₂} D'] [Category.{v₃} E]
variable (F : D ⥤ D') (S : MorphismProperty D) [S.ContainsIdentities]
variable (Q : D ⥤ E) [Q.IsLocalization S]

section Right

variable [F.HasPointwiseRightDerivedFunctor S]


/-- At an object which computes the right derived functor, the total right-derived unit is the
canonical comparison isomorphism. -/
@[stacks 05SX "the right-derived computation isomorphism"]
noncomputable def RightDerived.ComputesAt.unitIso
    (X : D) (hX : RightDerived.ComputesAt F S X) :
    F.obj X ≅ (F.totalRightDerived Q S).obj (Q.obj X) where
  hom := (F.totalRightDerivedUnit Q S).app X
  inv := by
    let e := Localization.compUniqFunctor S.Q Q S
    let G := (Localization.uniq S.Q Q S).functor ⋙ F.totalRightDerived Q S
    let β : F ⟶ S.Q ⋙ G :=
      F.totalRightDerivedUnit Q S ≫ whiskerRight e.inv _ ≫ (associator _ _ _).hom
    have : G.IsLeftKanExtension β :=
      (isLeftKanExtension_iff_postcomp₁ _ e (F.totalRightDerivedUnit Q S)).mp
        (IsRightDerivedFunctor.isLeftKanExtension _ _ S)
    have : G.IsRightDerivedFunctor β S := ⟨inferInstance⟩
    let eX : (F.totalRightDerived Q S).obj (Q.obj X) ≅ RightDerived.Value.obj F S X :=
      (F.totalRightDerived Q S).mapIso (e.app X).symm ≪≫
        ((isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor
          (F' := G) (F := F) (L := S.Q) (α := β) S) (S.Q.obj X)).isoColimit
    exact eX.hom ≫ (RightDerived.ComputesAt.valueIsoOf F S X hX).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward computation isomorphism is the total right-derived unit. -/
@[simp]
theorem RightDerived.ComputesAt.unitIso_hom
    (X : D) (hX : RightDerived.ComputesAt F S X) :
    (RightDerived.ComputesAt.unitIso F S Q X hX).hom =
      (F.totalRightDerivedUnit Q S).app X := rfl

/-- The inverse computation isomorphism is the inverse of the total right-derived unit. -/
@[simp]
theorem RightDerived.ComputesAt.unitIso_inv
    (X : D) (hX : RightDerived.ComputesAt F S X) :
    (RightDerived.ComputesAt.unitIso F S Q X hX).inv =
      @CategoryTheory.inv _ _ _ _ ((F.totalRightDerivedUnit Q S).app X)
        (RightDerived.ComputesAt.unitIso F S Q X hX).isIso_hom := sorry

/-- A local replacement by an object computing the right derived functor computes the total
right-derived value at the original object. -/
@[stacks 05SX "computing a total right-derived value by a local replacement"]
noncomputable def RightDerived.ComputesAt.replacementIso
    {X Y : D} (s : X ⟶ Y) (hs : S s)
    (hY : RightDerived.ComputesAt F S Y) :
    F.obj Y ≅ (F.totalRightDerived Q S).obj (Q.obj X) :=
  RightDerived.ComputesAt.unitIso F S Q Y hY ≪≫
    (F.totalRightDerived Q S).mapIso (Localization.isoOfHom Q S s hs).symm

/-- The forward replacement comparison is the derived unit followed by transport against the
localized replacement. -/
@[simp]
theorem RightDerived.ComputesAt.replacementIso_hom
    {X Y : D} (s : X ⟶ Y) (hs : S s)
    (hY : RightDerived.ComputesAt F S Y) :
    (RightDerived.ComputesAt.replacementIso F S Q s hs hY).hom =
      (F.totalRightDerivedUnit Q S).app Y ≫
        (F.totalRightDerived Q S).map (Localization.isoOfHom Q S s hs).inv := sorry

/-- The inverse replacement comparison transports along the localized replacement before using
the inverse derived unit. -/
@[simp]
theorem RightDerived.ComputesAt.replacementIso_inv
    {X Y : D} (s : X ⟶ Y) (hs : S s)
    (hY : RightDerived.ComputesAt F S Y) :
    (RightDerived.ComputesAt.replacementIso F S Q s hs hY).inv =
      (F.totalRightDerived Q S).map (Localization.isoOfHom Q S s hs).hom ≫
        (RightDerived.ComputesAt.unitIso F S Q Y hY).inv := sorry

/-- Replacement comparisons are natural with respect to commutative squares of local
replacements. -/
@[reassoc]
theorem RightDerived.ComputesAt.replacementIso_hom_naturality
    {X₁ X₂ Y₁ Y₂ : D}
    (sX : X₁ ⟶ X₂) (hsX : S sX) (hX₂ : RightDerived.ComputesAt F S X₂)
    (sY : Y₁ ⟶ Y₂) (hsY : S sY) (hY₂ : RightDerived.ComputesAt F S Y₂)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (comm : sX ≫ g = f ≫ sY) :
    F.map g ≫ (RightDerived.ComputesAt.replacementIso F S Q sY hsY hY₂).hom =
      (RightDerived.ComputesAt.replacementIso F S Q sX hsX hX₂).hom ≫
        (F.totalRightDerived Q S).map (Q.map f) := sorry

/-- The inverse replacement comparisons satisfy the reverse naturality square. -/
@[reassoc]
theorem RightDerived.ComputesAt.replacementIso_inv_naturality
    {X₁ X₂ Y₁ Y₂ : D}
    (sX : X₁ ⟶ X₂) (hsX : S sX) (hX₂ : RightDerived.ComputesAt F S X₂)
    (sY : Y₁ ⟶ Y₂) (hsY : S sY) (hY₂ : RightDerived.ComputesAt F S Y₂)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (comm : sX ≫ g = f ≫ sY) :
    (RightDerived.ComputesAt.replacementIso F S Q sX hsX hX₂).inv ≫ F.map g =
      (F.totalRightDerived Q S).map (Q.map f) ≫
        (RightDerived.ComputesAt.replacementIso F S Q sY hsY hY₂).inv := sorry

end Right

section Left

variable [F.HasPointwiseLeftDerivedFunctor S]


/-- At an object which computes the left derived functor, the total left-derived counit is the
canonical comparison isomorphism. -/
@[stacks 05SX "the left-derived computation isomorphism"]
noncomputable def LeftDerived.ComputesAt.counitIso
    (X : D) (hX : LeftDerived.ComputesAt F S X) :
    (F.totalLeftDerived Q S).obj (Q.obj X) ≅ F.obj X where
  hom := (F.totalLeftDerivedCounit Q S).app X
  inv := by
    let e := Localization.compUniqFunctor S.Q Q S
    let G := (Localization.uniq S.Q Q S).functor ⋙ F.totalLeftDerived Q S
    let β : S.Q ⋙ G ⟶ F :=
      (associator _ _ _).inv ≫ whiskerRight e.hom _ ≫ F.totalLeftDerivedCounit Q S
    have : G.IsRightKanExtension β :=
      (isRightKanExtension_iff_postcomp₁ _ e (F.totalLeftDerivedCounit Q S)).mp
        (IsLeftDerivedFunctor.isRightKanExtension _ _ S)
    have : G.IsLeftDerivedFunctor β S := ⟨inferInstance⟩
    let eX : (F.totalLeftDerived Q S).obj (Q.obj X) ≅ LeftDerived.Value.obj F S X :=
      (F.totalLeftDerived Q S).mapIso (e.app X).symm ≪≫
        ((isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor
          (F' := G) (F := F) (L := S.Q) (α := β) S) (S.Q.obj X)).isoLimit
    exact (LeftDerived.ComputesAt.valueIsoOf F S X hX).inv ≫ eX.inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward computation isomorphism is the total left-derived counit. -/
@[simp]
theorem LeftDerived.ComputesAt.counitIso_hom
    (X : D) (hX : LeftDerived.ComputesAt F S X) :
    (LeftDerived.ComputesAt.counitIso F S Q X hX).hom =
      (F.totalLeftDerivedCounit Q S).app X := rfl

/-- The inverse computation isomorphism is the inverse of the total left-derived counit. -/
@[simp]
theorem LeftDerived.ComputesAt.counitIso_inv
    (X : D) (hX : LeftDerived.ComputesAt F S X) :
    (LeftDerived.ComputesAt.counitIso F S Q X hX).inv =
      @CategoryTheory.inv _ _ _ _ ((F.totalLeftDerivedCounit Q S).app X)
        (LeftDerived.ComputesAt.counitIso F S Q X hX).isIso_hom := sorry

/-- A local coreplacement by an object computing the left derived functor computes the total
left-derived value at the target object. -/
@[stacks 05SX "computing a total left-derived value by a local coreplacement"]
noncomputable def LeftDerived.ComputesAt.coreplacementIso
    {X Y : D} (s : X ⟶ Y) (hs : S s)
    (hX : LeftDerived.ComputesAt F S X) :
    (F.totalLeftDerived Q S).obj (Q.obj Y) ≅ F.obj X :=
  (F.totalLeftDerived Q S).mapIso (Localization.isoOfHom Q S s hs).symm ≪≫
    LeftDerived.ComputesAt.counitIso F S Q X hX

/-- The forward coreplacement comparison transports against the localized coreplacement and
then applies the left-derived counit. -/
@[simp]
theorem LeftDerived.ComputesAt.coreplacementIso_hom
    {X Y : D} (s : X ⟶ Y) (hs : S s)
    (hX : LeftDerived.ComputesAt F S X) :
    (LeftDerived.ComputesAt.coreplacementIso F S Q s hs hX).hom =
      (F.totalLeftDerived Q S).map (Localization.isoOfHom Q S s hs).inv ≫
        (F.totalLeftDerivedCounit Q S).app X := sorry

/-- The inverse coreplacement comparison first uses the inverse left-derived counit and then
transports along the localized coreplacement. -/
@[simp]
theorem LeftDerived.ComputesAt.coreplacementIso_inv
    {X Y : D} (s : X ⟶ Y) (hs : S s)
    (hX : LeftDerived.ComputesAt F S X) :
    (LeftDerived.ComputesAt.coreplacementIso F S Q s hs hX).inv =
      (LeftDerived.ComputesAt.counitIso F S Q X hX).inv ≫
        (F.totalLeftDerived Q S).map (Localization.isoOfHom Q S s hs).hom := sorry

/-- Coreplacement comparisons are natural with respect to commutative squares of local
coreplacements. -/
@[reassoc]
theorem LeftDerived.ComputesAt.coreplacementIso_hom_naturality
    {X₁ X₂ Y₁ Y₂ : D}
    (sX : X₁ ⟶ X₂) (hsX : S sX) (hX₁ : LeftDerived.ComputesAt F S X₁)
    (sY : Y₁ ⟶ Y₂) (hsY : S sY) (hY₁ : LeftDerived.ComputesAt F S Y₁)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (comm : sX ≫ g = f ≫ sY) :
    (F.totalLeftDerived Q S).map (Q.map g) ≫
        (LeftDerived.ComputesAt.coreplacementIso F S Q sY hsY hY₁).hom =
      (LeftDerived.ComputesAt.coreplacementIso F S Q sX hsX hX₁).hom ≫ F.map f := sorry

/-- The inverse coreplacement comparisons satisfy the reverse naturality square. -/
@[reassoc]
theorem LeftDerived.ComputesAt.coreplacementIso_inv_naturality
    {X₁ X₂ Y₁ Y₂ : D}
    (sX : X₁ ⟶ X₂) (hsX : S sX) (hX₁ : LeftDerived.ComputesAt F S X₁)
    (sY : Y₁ ⟶ Y₂) (hsY : S sY) (hY₁ : LeftDerived.ComputesAt F S Y₁)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (comm : sX ≫ g = f ≫ sY) :
    (LeftDerived.ComputesAt.coreplacementIso F S Q sX hsX hX₁).inv ≫
        (F.totalLeftDerived Q S).map (Q.map g) =
      F.map f ≫ (LeftDerived.ComputesAt.coreplacementIso F S Q sY hsY hY₁).inv := sorry

end Left

end CategoryTheory.Functor
