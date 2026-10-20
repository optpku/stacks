module

public import ReasLib.CategoryTheory.Functor.Derived.Model

/-! # Derived functors from augmented replacements

A computation isomorphism for an augmented replacement specifies every universal extension
map. Acyclicity of the augmentation on replacement objects gives uniqueness.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe uC vC uD vD uH vH

namespace CategoryTheory.Functor.LeftDerived.Deformation

variable {C : Type uC} {D : Type uD} {H : Type uH}
  [Category.{vC} C] [Category.{vD} D] [Category.{vH} H]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
  (R : C ⥤ C) (η : R ⟶ 𝟭 C) (hη : ∀ A, W (η.app A))
  (F : C ⥤ H) (T : D ⥤ H) (e : L ⋙ T ≅ R ⋙ F)

/-- The computation comparison followed by the image of the replacement augmentation. -/
def counit : L ⋙ T ⟶ F :=
  e.hom ≫ whiskerRight η F ≫ (leftUnitor F).hom

/-- Reverse the localized augmentation, evaluate the supplied comparison on the replacement,
and reverse the computation isomorphism. -/
def extensionLiftOnInput (G : D ⥤ H) (β : L ⋙ G ⟶ F) (A : C) :
    G.obj (L.obj A) ⟶ T.obj (L.obj A) :=
  G.map (Localization.isoOfHom L W (η.app A) (hη A)).inv ≫
    β.app (R.obj A) ≫ (e.app A).inv

/-- The augmentation-based extension maps are natural in the original input. -/
theorem extensionLiftOnInput_naturality (G : D ⥤ H) (β : L ⋙ G ⟶ F)
    {A B : C} (a : A ⟶ B) :
    (L ⋙ G).map a ≫ extensionLiftOnInput L W R η hη F T e G β B =
      extensionLiftOnInput L W R η hη F T e G β A ≫ (L ⋙ T).map a := sorry

/-- Localization descent of the specified augmentation-based extension maps. -/
def extensionLift (G : D ⥤ H) (β : L ⋙ G ⟶ F) : G ⟶ T :=
  Localization.liftNatTrans L W (L ⋙ G) (L ⋙ T) G T
    { app := extensionLiftOnInput L W R η hη F T e G β
      naturality := fun _ _ a ↦
        extensionLiftOnInput_naturality L W R η hη F T e G β a }

/-- The descended extension maps recover the given comparison after composition with the counit. -/
theorem extensionLift_fac (G : D ⥤ H) (β : L ⋙ G ⟶ F) :
    whiskerLeft L (extensionLift L W R η hη F T e G β) ≫
      counit L R η F T e = β := sorry

/-- The right-extension arrow whose underlying map is the specified localization lift. -/
def terminalExtensionLift (E : RightExtension L F) :
    E ⟶ RightExtension.mk T (counit L R η F T e) :=
  CostructuredArrow.homMk (extensionLift L W R η hη F T e E.left E.hom)
    (extensionLift_fac L W R η hη F T e E.left E.hom)

variable (hAug : ∀ A, IsIso (F.map (η.app (R.obj A))))

include hAug in
/-- Acyclicity on replacement objects makes every right-extension arrow equal to the specified lift. -/
theorem terminalExtensionLift_unique (E : RightExtension L F)
    (m : E ⟶ RightExtension.mk T (counit L R η F T e)) :
    m = terminalExtensionLift L W R η hη F T e E := sorry

/-- The terminal witness stores the augmentation-based maps and their universal laws. -/
def terminalWitness : (RightExtension.mk T (counit L R η F T e)).IsUniversal :=
  IsTerminal.ofUniqueHom (terminalExtensionLift L W R η hη F T e)
    (terminalExtensionLift_unique L W R η hη F T e hAug)

include hη hAug in
/-- The specified computation and augmentation exhibit the constructed functor as left derived. -/
theorem isLeftDerived : T.IsLeftDerivedFunctor (counit L R η F T e) W where
  isRightKanExtension := { nonempty_isUniversal := ⟨terminalWitness L W R η hη F T e hAug⟩ }

end CategoryTheory.Functor.LeftDerived.Deformation

namespace CategoryTheory.Functor.LeftDerived.Deformation

universe uB vB

/-- A specified terminal extension after precomposition with a localization gives a terminal
extension before precomposition, with exactly the same underlying extension maps. -/
def terminalWitnessOfPrecomp
    {B : Type uB} {C : Type uC} {D : Type uD} {H : Type uH}
    [Category.{vB} B] [Category.{vC} C] [Category.{vD} D] [Category.{vH} H]
    (q : B ⥤ C) (V : MorphismProperty B) [q.IsLocalization V]
    (L : C ⥤ D) (F : C ⥤ H) (T : D ⥤ H) (ε : L ⋙ T ⟶ F)
    (w : (RightExtension.mk T ((associator q L T).hom ≫ whiskerLeft q ε)).IsUniversal) :
    (RightExtension.mk T ε).IsUniversal := by
  let lift (E : RightExtension L F) : E.left ⟶ T :=
    w.lift (RightExtension.mk E.left
      ((associator q L E.left).hom ≫ whiskerLeft q E.hom))
  have fac (E : RightExtension L F) : whiskerLeft L (lift E) ≫ ε = E.hom := by
    apply Localization.natTrans_ext q V
    intro A
    have h := NatTrans.congr_app (w.fac
      (RightExtension.mk E.left
        ((associator q L E.left).hom ≫ whiskerLeft q E.hom))) A
    change (lift E).app (L.obj (q.obj A)) ≫ (𝟙 _ ≫ ε.app (q.obj A)) =
      𝟙 _ ≫ E.hom.app (q.obj A) at h
    change (lift E).app (L.obj (q.obj A)) ≫ ε.app (q.obj A) = E.hom.app (q.obj A)
    simpa only [Category.id_comp] using h
  exact IsTerminal.ofUniqueHom
    (fun E ↦ CostructuredArrow.homMk (lift E) (fac E))
    (fun E m ↦ CostructuredArrow.hom_ext _ _ (by
      apply w.hom_ext
      ext A
      have h := NatTrans.congr_app (CostructuredArrow.w m) (q.obj A)
      have h' := NatTrans.congr_app (fac E) (q.obj A)
      change m.left.app (L.obj (q.obj A)) ≫ ε.app (q.obj A) = E.hom.app (q.obj A) at h
      change (lift E).app (L.obj (q.obj A)) ≫ ε.app (q.obj A) = E.hom.app (q.obj A) at h'
      change m.left.app (L.obj (q.obj A)) ≫ (𝟙 _ ≫ ε.app (q.obj A)) =
        (lift E).app (L.obj (q.obj A)) ≫ (𝟙 _ ≫ ε.app (q.obj A))
      simpa only [Category.id_comp] using h.trans h'.symm))

/-- Descend a specified augmented replacement model through a localization of its source.
All universal extension maps are those of the given augmented replacement construction. -/
def modelOnLocalizedSource
    {B : Type uB} {C : Type uC} {D : Type uD} {H : Type uH}
    [Category.{vB} B] [Category.{vC} C] [Category.{vD} D] [Category.{vH} H]
    (q : B ⥤ C) (V : MorphismProperty B) [q.IsLocalization V]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    (U : MorphismProperty B) [(q ⋙ L).IsLocalization U]
    (R : B ⥤ B) (η : R ⟶ 𝟭 B) (hη : ∀ A, U (η.app A))
    (F : C ⥤ H) (T : D ⥤ H) (e : (q ⋙ L) ⋙ T ≅ R ⋙ (q ⋙ F))
    (hAug : ∀ A, IsIso ((q ⋙ F).map (η.app (R.obj A)))) :
    LeftDerived.Model F L W := by
  let ε₀ := counit (q ⋙ L) R η (q ⋙ F) T e
  let ε : L ⋙ T ⟶ F := Localization.liftNatTrans q V
    (q ⋙ (L ⋙ T)) (q ⋙ F) (L ⋙ T) F
    ((associator q L T).inv ≫ ε₀)
  have hε : (associator q L T).hom ≫ whiskerLeft q ε = ε₀ := by
    ext A
    simp [ε, Localization.liftNatTrans_app]
  let w := terminalWitness (q ⋙ L) U R η hη (q ⋙ F) T e hAug
  refine ⟨T, ε, ?_⟩
  refine { isRightKanExtension := { nonempty_isUniversal := ?_ } }
  exact ⟨terminalWitnessOfPrecomp q V L F T ε
    (hε ▸ w)⟩


end CategoryTheory.Functor.LeftDerived.Deformation
