module

public import ReasLib.CategoryTheory.Sites.GlobalSections.ToposMorphism
public import ReasLib.CategoryTheory.Sites.Topos.Abelian
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Integer

/-! # Abelian global sections under morphisms of topoi -/

set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v u' v' w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J AddCommGrpCat.{w}] [HasWeakSheafify J (Type w)]
variable [J.HasSheafCompose (forget AddCommGrpCat.{w})]
variable [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor J (Type w)]

private def globalSectionsToUnderlying (F : Sheaf J AddCommGrpCat.{w})
    (x : (Γ J AddCommGrpCat.{w}).obj F) :
    (Γ J (Type w)).obj ((sheafCompose J (forget AddCommGrpCat.{w})).obj F) :=
  (ΓObjEquivSections J _).symm
    ⟨fun V ↦ ΓRes F V x, fun {_ _} g ↦
      ConcreteCategory.congr_hom (ΓRes_map F g) x⟩

private def globalSectionsFromUnderlying (F : Sheaf J AddCommGrpCat.{w})
    (x : (Γ J (Type w)).obj ((sheafCompose J (forget AddCommGrpCat.{w})).obj F)) :
    (Γ J AddCommGrpCat.{w}).obj F :=
  (globalSectionsEquivConstantIntegerSheafHomOnSite J F).symm
    (((sheafificationAdjunction J AddCommGrpCat.{w}).homEquiv _ _).symm
      { app := fun V ↦ AddCommGrpCat.ofHom
          (uliftZMultiplesHom (F.obj.obj V) ((ΓObjEquivSections J _ x).val V))
        naturality := by
          intro V W g
          ext n
          change uliftZMultiplesHom (F.obj.obj W) ((ΓObjEquivSections J _ x).val W) n =
            (F.obj.map g)
              (uliftZMultiplesHom (F.obj.obj V) ((ΓObjEquivSections J _ x).val V) n)
          simp only [uliftZMultiplesHom_apply_apply, map_zsmul]
          exact congrArg (fun y : F.obj.obj W ↦ n.down • y)
            ((ΓObjEquivSections J _ x).property g).symm })

/-- Restricting abelian global sections and reconstructing them from integer multiples
are inverse operations and commute with sheaf morphisms. -/
private theorem globalSectionsForget_laws :
    (∀ (F : Sheaf J AddCommGrpCat.{w}),
      Function.LeftInverse (globalSectionsFromUnderlying J F) (globalSectionsToUnderlying J F)) ∧
    (∀ (F : Sheaf J AddCommGrpCat.{w}),
      Function.RightInverse (globalSectionsFromUnderlying J F) (globalSectionsToUnderlying J F)) ∧
    (∀ {F G : Sheaf J AddCommGrpCat.{w}} (α : F ⟶ G)
      (x : (Γ J AddCommGrpCat.{w}).obj F),
      globalSectionsToUnderlying J G ((Γ J AddCommGrpCat.{w}).map α x) =
        (Γ J (Type w)).map ((sheafCompose J (forget AddCommGrpCat.{w})).map α)
          (globalSectionsToUnderlying J F x)) := sorry

/-- Abelian global sections are canonically equivalent to global sections of the
underlying sheaf of types. -/
def globalSectionsForgetEquiv (F : Sheaf J AddCommGrpCat.{w}) :
    (Γ J AddCommGrpCat.{w}).obj F ≃
      (Γ J (Type w)).obj ((sheafCompose J (forget AddCommGrpCat.{w})).obj F) where
  toFun := globalSectionsToUnderlying J F
  invFun := globalSectionsFromUnderlying J F
  left_inv := (globalSectionsForget_laws J).1 F
  right_inv := (globalSectionsForget_laws J).2.1 F

end CategoryTheory.Sheaf

namespace CategoryTheory.MorphismOfTopoiIn

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable [HasWeakSheafify J AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]
variable [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
variable [J.HasSheafCompose (forget AddCommGrpCat.{w})]
variable [K.HasSheafCompose (forget AddCommGrpCat.{w})]
variable [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor K AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor J (Type w)] [HasGlobalSectionsFunctor K (Type w)]
variable (f : MorphismOfTopoiIn.{u, u', v, v', w} J K)

/-- Transporting global sections through the underlying-sheaf comparison and the
topos adjunction respects addition and sheaf morphisms. -/
private theorem abelianPushforwardGlobalSections_laws :
    (∀ (F : Sheaf K AddCommGrpCat.{w}),
      let e := (Sheaf.globalSectionsForgetEquiv J (f.abelianDirectImage.obj F)).trans
        (((Sheaf.Γ J (Type w)).mapIso (f.abelianDirectImageForgetIso.app F)).toEquiv.trans
          ((f.pushforwardCompΓIso.app
              ((sheafCompose K (forget AddCommGrpCat.{w})).obj F)).toEquiv.trans
            (Sheaf.globalSectionsForgetEquiv K F).symm))
      ∀ x y, e (x + y) = e x + e y) ∧
    (∀ {F G : Sheaf K AddCommGrpCat.{w}} (α : F ⟶ G)
      (x : (Sheaf.Γ J AddCommGrpCat.{w}).obj (f.abelianDirectImage.obj F)),
      let e := fun H : Sheaf K AddCommGrpCat.{w} ↦
        (Sheaf.globalSectionsForgetEquiv J (f.abelianDirectImage.obj H)).trans
          (((Sheaf.Γ J (Type w)).mapIso (f.abelianDirectImageForgetIso.app H)).toEquiv.trans
            ((f.pushforwardCompΓIso.app
                ((sheafCompose K (forget AddCommGrpCat.{w})).obj H)).toEquiv.trans
              (Sheaf.globalSectionsForgetEquiv K H).symm))
      e G ((Sheaf.Γ J AddCommGrpCat.{w}).map (f.abelianDirectImage.map α) x) =
        (Sheaf.Γ K AddCommGrpCat.{w}).map α (e F x)) := sorry

/-- Abelian direct image followed by global sections is canonically isomorphic
to global sections on the source topos. -/
def abelianPushforwardCompΓIso :
    f.abelianDirectImage ⋙ Sheaf.Γ J AddCommGrpCat.{w} ≅
      Sheaf.Γ K AddCommGrpCat.{w} :=
  NatIso.ofComponents (fun F ↦
    (AddEquiv.mk' ((Sheaf.globalSectionsForgetEquiv J (f.abelianDirectImage.obj F)).trans
      (((Sheaf.Γ J (Type w)).mapIso (f.abelianDirectImageForgetIso.app F)).toEquiv.trans
        ((f.pushforwardCompΓIso.app
            ((sheafCompose K (forget AddCommGrpCat.{w})).obj F)).toEquiv.trans
          (Sheaf.globalSectionsForgetEquiv K F).symm)))
      ((abelianPushforwardGlobalSections_laws f).1 F)).toAddCommGrpIso)
    (by intro F G α; ext x; exact (abelianPushforwardGlobalSections_laws f).2 α x)

/-- The direct-image comparison restricts to underlying type-valued global
sections, transports along direct image, and reconstructs abelian sections. -/
theorem abelianPushforwardCompΓIso_hom_apply (F : Sheaf K AddCommGrpCat.{w})
    (x : (Sheaf.Γ J AddCommGrpCat.{w}).obj (f.abelianDirectImage.obj F)) :
    (f.abelianPushforwardCompΓIso.hom.app F) x =
      (Sheaf.globalSectionsForgetEquiv K F).symm
        ((f.pushforwardCompΓIso.hom.app
            ((sheafCompose K (forget AddCommGrpCat.{w})).obj F))
          ((Sheaf.Γ J (Type w)).map (f.abelianDirectImageForgetIso.hom.app F)
            (Sheaf.globalSectionsForgetEquiv J (f.abelianDirectImage.obj F) x))) := rfl

end CategoryTheory.MorphismOfTopoiIn
