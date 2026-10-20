module

public import ReasLib.CategoryTheory.Sites.SheafGroupoid.Quotient
public import ReasLib.CategoryTheory.Fibered.Pushforward.InGroupoids
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Existence
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Stackification
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import Mathlib.CategoryTheory.Localization.Construction

/-!
# Quotient stacks and inverse image

The unit of continuous sheaf inverse image sends a section over `T` to a
section over `u(T)`. Restriction along `T' ⟶ u(T)` defines a functor from
the prelocalized pushforward to the inverse-image section prestack. Localization
and stackification give the comparison of quotient stacks.
-/

@[expose] public section

noncomputable section

universe uC vC uD vD a w

namespace CategoryTheory.SheafGroupoid

open Limits Opposite Pseudofunctor.CoGrothendieck

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [u.IsContinuous J K] [HasWeakSheafify K (Type a)]
variable [∀ P : Cᵒᵖ ⥤ Type a, u.op.HasLeftKanExtension P]
variable [PreservesFiniteLimits (u.sheafPullback (Type a) J K)]
variable [HasPullbacks (Sheaf J (Type a))] [HasPullbacks (Sheaf K (Type a))]
variable {B : Sheaf J (Type a)}

/-- The inverse-image internal groupoid along a continuous left-exact sheaf
pullback. Its operations are the transported internal operations. -/
abbrev inverseImage (G : SheafGroupoid J B) :
    SheafGroupoid K ((u.sheafPullback (Type a) J K).obj B) :=
  G.map (u.sheafPullback (Type a) J K)

/-- A section transported by the sheaf-adjunction unit and then restricted
along a morphism into the image of its original domain. -/
def inverseImageSection (F : Sheaf J (Type a)) {T : C} {T' : D}
    (φ : T' ⟶ u.obj T) (x : F.obj.obj (op T)) :
    ((u.sheafPullback (Type a) J K).obj F).obj.obj (op T') :=
  ((u.sheafPullback (Type a) J K).obj F).obj.map φ.op
    ((u.sheafPushforwardContinuousObjObjIso (Type a)
      ((u.sheafPullback (Type a) J K).obj F) T).hom
      (((u.sheafAdjunctionContinuous (Type a) J K).unit.app F).hom.app (op T) x))

/-- The object formula for the prelocalized comparison sends `(T', φ, x)` to
the inverse-image section obtained by the unit followed by restriction along `φ`. -/
def pushforwardSourceToInverseImageObj (G : SheafGroupoid J B)
    (Y : Functor.pushforwardSource u G.prestack.p) :
    ∫ᶜ (((inverseImage u J K G).points ⋙ Grpd.forgetToCat).toPseudofunctor') where
  base := Y.fst.left
  fiber := inverseImageSection u J K G.U.left Y.fst.hom
    (G.U.left.obj.map Y.iso.hom.op Y.snd.fiber)

/-- The unit-and-restriction formula for arrow sections has the endpoints of
the corresponding co-Grothendieck morphism. -/
theorem pushforwardSourceToInverseImageMap_endpoints (G : SheafGroupoid J B)
    {Y Z : Functor.pushforwardSource u G.prestack.p} (f : Y ⟶ Z) :
    (inverseImage u J K G).s.left.hom.app (op Y.fst.left)
        (inverseImageSection u J K G.R.left Y.fst.hom
          (G.R.left.obj.map Y.iso.hom.op f.snd.fiber.arrow)) =
      (pushforwardSourceToInverseImageObj u J K G Y).fiber ∧
    (inverseImage u J K G).t.left.hom.app (op Y.fst.left)
        (inverseImageSection u J K G.R.left Y.fst.hom
          (G.R.left.obj.map Y.iso.hom.op f.snd.fiber.arrow)) =
      (inverseImage u J K G).U.left.obj.map f.fst.left.op
        (pushforwardSourceToInverseImageObj u J K G Z).fiber := by
  sorry

/-- The arrow formula for the prelocalized comparison is the image of the
arrow section under the unit followed by restriction to the source domain. -/
def pushforwardSourceToInverseImageMap (G : SheafGroupoid J B)
    {Y Z : Functor.pushforwardSource u G.prestack.p} (f : Y ⟶ Z) :
    pushforwardSourceToInverseImageObj u J K G Y ⟶
      pushforwardSourceToInverseImageObj u J K G Z where
  base := f.fst.left
  fiber :=
    { arrow := inverseImageSection u J K G.R.left Y.fst.hom
        (G.R.left.obj.map Y.iso.hom.op f.snd.fiber.arrow)
      source := (pushforwardSourceToInverseImageMap_endpoints u J K G f).1
      target := (pushforwardSourceToInverseImageMap_endpoints u J K G f).2 }

/-- The unit-and-restriction object and arrow formulas preserve identities
and composition in the prelocalized pushforward category. -/
theorem pushforwardSourceToInverseImageFunctor_laws (G : SheafGroupoid J B) :
    (∀ Y : Functor.pushforwardSource u G.prestack.p,
      pushforwardSourceToInverseImageMap u J K G (𝟙 Y) =
        𝟙 (pushforwardSourceToInverseImageObj u J K G Y)) ∧
    (∀ (Y Z W : Functor.pushforwardSource u G.prestack.p) (f : Y ⟶ Z) (g : Z ⟶ W),
      pushforwardSourceToInverseImageMap u J K G (f ≫ g) =
        pushforwardSourceToInverseImageMap u J K G f ≫
          pushforwardSourceToInverseImageMap u J K G g) := by
  sorry

/-- The prelocalized comparison from the pushforward section category to
the section category of the inverse-image internal groupoid. -/
def pushforwardSourceToInverseImageFunctor (G : SheafGroupoid J B) :
    Functor.pushforwardSource u G.prestack.p ⥤
      ∫ᶜ (((inverseImage u J K G).points ⋙ Grpd.forgetToCat).toPseudofunctor') where
  obj := pushforwardSourceToInverseImageObj u J K G
  map := pushforwardSourceToInverseImageMap u J K G
  map_id := (pushforwardSourceToInverseImageFunctor_laws u J K G).1
  map_comp := (pushforwardSourceToInverseImageFunctor_laws u J K G).2 _ _ _

/-- The prelocalized comparison sends every pushforward fraction to an
isomorphism in the inverse-image section category. -/
theorem pushforwardSourceToInverseImageFunctor_inverts (G : SheafGroupoid J B) :
    (u.pushforwardFractions G.prestack.p).IsInvertedBy
      (pushforwardSourceToInverseImageFunctor u J K G) := by
  sorry

variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

omit [∀ P : Cᵒᵖ ⥤ Type a, u.op.HasLeftKanExtension P] in
/-- The groupoid-fibred projection choice for the localized pushforward of
the section prestack. -/
theorem prestackPushforwardChoice (G : SheafGroupoid J B) :
    FiberedCategoryOver.Groupoids.Pushforward.ProjectionChoice u G.prestack :=
  FiberedCategoryOver.Groupoids.Pushforward.ProjectionChoice.canonical u G.prestack

/-- The localized pushforward of the section prestack along the site functor. -/
def inverseImagePrestack (G : SheafGroupoid J B) : FiberedCategoryOver.Groupoids D :=
  FiberedCategoryOver.Groupoids.pushforward u G.prestack
    (prestackPushforwardChoice u J G)

/-- The localization lift of the unit-and-restriction comparison commutes
strictly with the projections to the larger site. -/
theorem pushforwardToInverseImagePrestack_over (G : SheafGroupoid J B) :
    Localization.Construction.lift (pushforwardSourceToInverseImageFunctor u J K G)
        (pushforwardSourceToInverseImageFunctor_inverts u J K G) ⋙
      (inverseImage u J K G).prestack.p = (inverseImagePrestack u J G).p := by
  sorry

/-- The localized unit-and-restriction comparison, regarded as a functor over
the larger site. -/
def pushforwardToInverseImagePrestackBased (G : SheafGroupoid J B) :
    BasedCategory.ofFunctor (inverseImagePrestack u J G).p ⥤ᵇ
      BasedCategory.ofFunctor (inverseImage u J K G).prestack.p :=
  BasedFunctor.ofFunctor
    (Localization.Construction.lift (pushforwardSourceToInverseImageFunctor u J K G)
      (pushforwardSourceToInverseImageFunctor_inverts u J K G))
    (pushforwardToInverseImagePrestack_over u J K G)

/-- The localized comparison preserves strongly cartesian morphisms. -/
theorem pushforwardToInverseImagePrestack_cartesian (G : SheafGroupoid J B) :
    (pushforwardToInverseImagePrestackBased u J K G).PreservesStronglyCartesian := by
  sorry

/-- The cartesian comparison from the localized section pushforward to the
section prestack of the inverse-image groupoid. -/
def pushforwardToInverseImagePrestack (G : SheafGroupoid J B) :
    CartesianBasedFunctor (inverseImagePrestack u J G).p
      (inverseImage u J K G).prestack.p :=
  CartesianBasedFunctor.ofBasedFunctor
    (pushforwardToInverseImagePrestackBased u J K G)
    (pushforwardToInverseImagePrestack_cartesian u J K G)

/-- The cartesian comparison from the localized section pushforward to the
quotient stack of the inverse-image internal groupoid. -/
def pushforwardToInverseImageQuotient (G : SheafGroupoid J B) :
    CartesianBasedFunctor (inverseImagePrestack u J G).p
      (inverseImage u J K G).quotientStack.p :=
  (pushforwardToInverseImagePrestack u J K G).comp
    (inverseImage u J K G).quotientStackPresentation.comparison

variable [Small.{w} D]

/-- The selected inverse image of the quotient stack along the site functor. -/
def quotientInverseImage (G : SheafGroupoid J B) :
    StackOver.InverseImage K u G.quotientStack.toStackOver :=
  StackOver.InverseImage.canonical u

/-- The stackification comparison from the localized section pushforward
to the inverse image of the original quotient stack. -/
def inverseImagePushforwardComparison (G : SheafGroupoid J B) :
    CartesianBasedFunctor (inverseImagePrestack u J G).p
      (quotientInverseImage u J K G).target.p :=
  StackOver.InverseImage.Cartesian.pushforwardComparison
    (quotientInverseImage u J K G)
    (Functor.Pushforward.ProjectionChoice.canonical u G.prestack.p)
    G.quotientStackPresentation.comparison
    (Functor.Pushforward.sourceMap.inverts.spec u G.quotientStackPresentation.comparison)

omit [HasWeakSheafify K (Type a)]
    [∀ P : Cᵒᵖ ⥤ Type a, u.op.HasLeftKanExtension P]
    [PreservesFiniteLimits (u.sheafPullback (Type a) J K)]
    [HasPullbacks (Sheaf K (Type a))] in
/-- The pushforward comparison is a stackification on the larger site. -/
theorem inverseImagePushforwardComparison_isStackification (G : SheafGroupoid J B) :
    CartesianBasedFunctor.IsStackification K
      (inverseImagePushforwardComparison u J K G) :=
  StackOver.InverseImage.Cartesian.pushforwardComparison.isStackification
    (quotientInverseImage u J K G) G.quotientStack_isStackification
    (Functor.Pushforward.ProjectionChoice.canonical u G.prestack.p)
    (Functor.Pushforward.sourceMap.inverts.spec u G.quotientStackPresentation.comparison)

/-- The stackification lift of the explicit localized comparison. -/
def quotientStackInverseImageLift (G : SheafGroupoid J B) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := inverseImagePushforwardComparison u J K G)
      (pushforwardToInverseImageQuotient u J K G) :=
  CartesianBasedFunctor.IsStackification.liftChoice
    (inverseImagePushforwardComparison_isStackification u J K G)
    (pushforwardToInverseImageQuotient u J K G)

/-- The comparison from the inverse image of the quotient stack to the quotient
stack of the inverse-image groupoid, obtained by localization and stackification. -/
def quotientStackInverseImageHom (G : SheafGroupoid J B) :
    CartesianBasedFunctor (quotientInverseImage u J K G).target.p
      (inverseImage u J K G).quotientStack.p :=
  (quotientStackInverseImageLift u J K G).lift

/-- Precomposing the stack comparison with the inverse-image stackification
comparison recovers the localized unit-and-restriction comparison up to isomorphism. -/
def quotientStackInverseImageHom_comp (G : SheafGroupoid J B) :
    (CartesianBasedFunctor.precomp (inverseImage u J K G).quotientStack.p
      (inverseImagePushforwardComparison u J K G)).obj
        (quotientStackInverseImageHom u J K G) ≅
      pushforwardToInverseImageQuotient u J K G :=
  (quotientStackInverseImageLift u J K G).comparison

/-- The quotient-stack inverse-image comparison admits a quasi-inverse over
the larger site. -/
theorem quotientStackInverseImage_equivalence (G : SheafGroupoid J B) :
    Nonempty (BasedFunctor.QuasiInverse
      (quotientStackInverseImageHom u J K G).toBasedFunctor) := by
  sorry

end CategoryTheory.SheafGroupoid
