module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Differentials.Relations
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits

@[expose] public section
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u v w

namespace SheafOfModules.DifferentialRelations
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (R : Sheaf J RingCat.{w})

/-- The source's free module sheaf: sheafify the pointwise free module presheaf. -/
abbrev freeSheaf (F : Cᵒᵖ ⥤ Type w) : SheafOfModules.{w} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj (PresheafOfModules.freeObj F)

/-- The local generator, mapped into the associated sheaf by the sheafification unit. -/
def generator (F : Cᵒᵖ ⥤ Type w) (U : Cᵒᵖ) (x : F.obj U) :
    (freeSheaf R F).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app
    (PresheafOfModules.freeObj F)).app U (ModuleCat.freeMk x)

/-- The free module sheaf on local ring sections. -/
abbrev generators : SheafOfModules.{w} R := freeSheaf R (R.obj ⋙ CategoryTheory.forget RingCat)

/-- The free module sheaf on pairs of local ring sections. -/
abbrev pairGenerators : SheafOfModules.{w} R :=
  freeSheaf R (PresheafOfModules.DifferentialRelations.pairs R.obj)

variable {R} {S : Sheaf J RingCat.{w}} (φ : S ⟶ R)

/-- The sheafified additivity-relation map. -/
def addMap : pairGenerators R ⟶ generators R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map
    (PresheafOfModules.DifferentialRelations.addMap R.obj)

/-- The sheafified Leibniz-relation map. -/
def mulMap : pairGenerators R ⟶ generators R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map
    (PresheafOfModules.DifferentialRelations.mulMap R.obj)

/-- The sheafified source-ring relation map. -/
def baseMap : freeSheaf R (S.obj ⋙ CategoryTheory.forget RingCat) ⟶ generators R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map
    (PresheafOfModules.DifferentialRelations.baseMap φ.hom)

/-- The three summands of relations in the displayed order. -/
abbrev relationSource : SheafOfModules.{w} R :=
  (pairGenerators R ⨿ pairGenerators R) ⨿ freeSheaf R (S.obj ⋙ CategoryTheory.forget RingCat)

/-- The canonical generator-relations map of Equation 18.33.2.1. -/
def relationMap : relationSource (R := R) (S := S) ⟶ generators R :=
  coprod.desc (coprod.desc addMap mulMap) (baseMap φ)

@[reassoc (attr := simp)] theorem add_inclusion_relationMap :
    (coprod.inl : pairGenerators R ⟶ pairGenerators R ⨿ pairGenerators R) ≫
      coprod.inl ≫ relationMap φ = addMap := by
  exact (congrArg (fun f ↦ coprod.inl ≫ f) (coprod.inl_desc
    (coprod.desc addMap mulMap) (baseMap φ))).trans (coprod.inl_desc addMap mulMap)

@[reassoc (attr := simp)] theorem mul_inclusion_relationMap :
    (coprod.inr : pairGenerators R ⟶ pairGenerators R ⨿ pairGenerators R) ≫
      coprod.inl ≫ relationMap φ = mulMap := by
  exact (congrArg (fun f ↦ coprod.inr ≫ f) (coprod.inl_desc
    (coprod.desc addMap mulMap) (baseMap φ))).trans (coprod.inr_desc addMap mulMap)

@[reassoc (attr := simp)] theorem base_inclusion_relationMap :
    coprod.inr ≫ relationMap φ = baseMap φ := by
  exact coprod.inr_desc (coprod.desc addMap mulMap) (baseMap φ)

variable (R)

/-- Naturality of the actual sheafification unit identifies values of a sheafified map. -/
theorem sheafifyMap_generator {F G : Cᵒᵖ ⥤ Type w}
    (f : PresheafOfModules.freeObj (R := R.obj) F ⟶ PresheafOfModules.freeObj G)
    (U : Cᵒᵖ) (x : F.obj U) :
    ((PresheafOfModules.sheafification (𝟙 R.obj)).map f).val.app U (generator R F U x) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app
        (PresheafOfModules.freeObj G)).app U (f.app U (ModuleCat.freeMk x)) := by
  exact (congrArg (fun k ↦ k.app U (ModuleCat.freeMk x))
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.naturality f)).symm

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem addMap_generator (U : Cᵒᵖ) (a b : R.obj.obj U) :
    (addMap (R := R)).val.app U
      (generator R (PresheafOfModules.DifferentialRelations.pairs R.obj) U (a,b)) =
    generator R (R.obj ⋙ CategoryTheory.forget RingCat) U (a+b) -
      generator R (R.obj ⋙ CategoryTheory.forget RingCat) U a - generator R (R.obj ⋙ CategoryTheory.forget RingCat) U b := by
  rw [addMap, sheafifyMap_generator, PresheafOfModules.DifferentialRelations.addMap_generator]
  simp only [map_sub]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem mulMap_generator (U : Cᵒᵖ) (f g : R.obj.obj U) :
    (mulMap (R := R)).val.app U
      (generator R (PresheafOfModules.DifferentialRelations.pairs R.obj) U (f,g)) =
    generator R (R.obj ⋙ CategoryTheory.forget RingCat) U (f*g) -
      g • generator R (R.obj ⋙ CategoryTheory.forget RingCat) U f -
      f • generator R (R.obj ⋙ CategoryTheory.forget RingCat) U g := by
  rw [mulMap, sheafifyMap_generator, PresheafOfModules.DifferentialRelations.mulMap_generator]
  simp only [map_sub, map_smul]
  rfl

@[simp] theorem baseMap_generator (U : Cᵒᵖ) (h : S.obj.obj U) :
    (baseMap φ).val.app U (generator R (S.obj ⋙ CategoryTheory.forget RingCat) U h) =
      generator R (R.obj ⋙ CategoryTheory.forget RingCat) U (φ.hom.app U h) := by
  rw [baseMap, sheafifyMap_generator, PresheafOfModules.DifferentialRelations.baseMap_generator]
  rfl

variable {R}

/-- A local generator in the first relation summand. -/
def addGenerator (U : Cᵒᵖ) (a b : R.obj.obj U) : (relationSource (R := R) (S := S)).val.obj U :=
  ((coprod.inl ≫ coprod.inl : pairGenerators R ⟶ relationSource (R := R) (S := S)).val.app U)
    (generator R (PresheafOfModules.DifferentialRelations.pairs R.obj) U (a,b))

/-- A local generator in the second relation summand. -/
def mulGenerator (U : Cᵒᵖ) (f g : R.obj.obj U) : (relationSource (R := R) (S := S)).val.obj U :=
  ((coprod.inr ≫ coprod.inl : pairGenerators R ⟶ relationSource (R := R) (S := S)).val.app U)
    (generator R (PresheafOfModules.DifferentialRelations.pairs R.obj) U (f,g))

/-- A local generator in the source-ring relation summand. -/
def baseGenerator (U : Cᵒᵖ) (h : S.obj.obj U) : (relationSource (R := R) (S := S)).val.obj U :=
  ((coprod.inr : freeSheaf R (S.obj ⋙ CategoryTheory.forget RingCat) ⟶ relationSource).val.app U)
    (generator R (S.obj ⋙ CategoryTheory.forget RingCat) U h)

theorem relationMap_addGenerator (U : Cᵒᵖ) (a b : R.obj.obj U) :
    (relationMap φ).val.app U (addGenerator (S := S) U a b) =
      generator R (R.obj ⋙ CategoryTheory.forget RingCat) U (a+b) -
        generator R (R.obj ⋙ CategoryTheory.forget RingCat) U a -
        generator R (R.obj ⋙ CategoryTheory.forget RingCat) U b :=
  (congrArg (fun k : pairGenerators R ⟶ generators R ↦ k.val.app U
      (generator R (PresheafOfModules.DifferentialRelations.pairs R.obj) U (a,b)))
    (add_inclusion_relationMap φ)).trans (addMap_generator R U a b)

theorem relationMap_mulGenerator (U : Cᵒᵖ) (f g : R.obj.obj U) :
    (relationMap φ).val.app U (mulGenerator (S := S) U f g) =
      generator R (R.obj ⋙ CategoryTheory.forget RingCat) U (f*g) -
        g • generator R (R.obj ⋙ CategoryTheory.forget RingCat) U f -
        f • generator R (R.obj ⋙ CategoryTheory.forget RingCat) U g :=
  (congrArg (fun k : pairGenerators R ⟶ generators R ↦ k.val.app U
      (generator R (PresheafOfModules.DifferentialRelations.pairs R.obj) U (f,g)))
    (mul_inclusion_relationMap φ)).trans (mulMap_generator R U f g)

theorem relationMap_baseGenerator (U : Cᵒᵖ) (h : S.obj.obj U) :
    (relationMap φ).val.app U (baseGenerator (R := R) U h) =
      generator R (R.obj ⋙ CategoryTheory.forget RingCat) U (φ.hom.app U h) :=
  (congrArg (fun k : freeSheaf R (S.obj ⋙ CategoryTheory.forget RingCat) ⟶ generators R ↦
      k.val.app U (generator R (S.obj ⋙ CategoryTheory.forget RingCat) U h))
    (base_inclusion_relationMap φ)).trans (baseMap_generator R φ U h)

set_option backward.isDefEq.respectTransparency false in
/-- The complete local-section formula displayed in Equation 18.33.2.1. -/
theorem relationMap_generators (U : Cᵒᵖ) (a b f g : R.obj.obj U) (h : S.obj.obj U) :
    (relationMap φ).val.app U
      (addGenerator (S := S) U a b + mulGenerator (S := S) U f g + baseGenerator (R := R) U h) =
      (generator R (R.obj ⋙ CategoryTheory.forget RingCat) U (a+b) -
        generator R (R.obj ⋙ CategoryTheory.forget RingCat) U a -
        generator R (R.obj ⋙ CategoryTheory.forget RingCat) U b) +
      (generator R (R.obj ⋙ CategoryTheory.forget RingCat) U (f*g) -
        g • generator R (R.obj ⋙ CategoryTheory.forget RingCat) U f -
        f • generator R (R.obj ⋙ CategoryTheory.forget RingCat) U g) +
      generator R (R.obj ⋙ CategoryTheory.forget RingCat) U (φ.hom.app U h) := by
  simp only [map_add, relationMap_addGenerator, relationMap_mulGenerator, relationMap_baseGenerator]

end SheafOfModules.DifferentialRelations
