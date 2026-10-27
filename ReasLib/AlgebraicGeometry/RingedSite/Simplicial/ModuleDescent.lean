/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Widesubcategory
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Cartesian
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.ModulePullback

/-!
# Face-descent data for cartesian modules on a ringed simplicial site

Pairs `(F, α)` consisting of an `O_0`-module and an isomorphism of `O_1`-modules between the
two coface pullbacks, together with the `O_2` cocycle.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites.Module

/-- The last-vertex operator sends the unique vertex to the last vertex. -/
def vertexOp (n : SimplexCategory) : ⦋0⦌ ⟶ n :=
  SimplexCategory.const ⦋0⦌ n (Fin.last n.len)

/-- The edge operator joins the image of the last vertex to the last target vertex. -/
def edgeOp {n m : SimplexCategory} (φ : n ⟶ m) : ⦋1⦌ ⟶ m :=
  SimplexCategory.mkOfLe (φ.toOrderHom (Fin.last n.len)) (Fin.last m.len) (Fin.le_last _)

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [instMorphismDiagram : IsMorphismDiagram.{u, v, w} C J]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (stageMorphism C J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]
include instMorphismDiagram instWeakSheafify instLeftKan

/-- Reidentify `f_φ^*` along an equality of simplex operators. -/
def recodeModulePullback {m n : SimplexCategory} {φ ψ : m ⟶ n} (h : φ = ψ) :
    (ringedToposMap C J O φ).modulePullback ≅
      (ringedToposMap C J O ψ).modulePullback :=
  eqToIso (congrArg (fun t : m ⟶ n ↦ (ringedToposMap C J O t).modulePullback) h)

/-- `recodeModulePullback` is the identity when the operator equality is `rfl`. -/
theorem recodeModulePullback_refl {m n : SimplexCategory} (φ : m ⟶ n) :
    recodeModulePullback C J O (rfl : φ = φ) = Iso.refl _ :=
  sorry

/-- The pullback of `α` along a 2-face `δ i`, as a morphism of `O_2`-modules. -/
def facePullback (i : Fin 3)
    {F : SheafOfModules.{w} (componentRingedSite C J O ⦋0⦌).structureSheaf}
    (α : (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullback.obj F ≅
      (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullback.obj F) :
    (ringedToposMap C J O
        (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ i)).modulePullback.obj F ⟶
      (ringedToposMap C J O
        (SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ i)).modulePullback.obj F :=
  (ringedModulePullbackCompIso C J O (SimplexCategory.δ (1 : Fin 2))
        (SimplexCategory.δ i)).hom.app F ≫
    (ringedToposMap C J O (SimplexCategory.δ i)).modulePullback.map α.hom ≫
    (ringedModulePullbackCompIso C J O (SimplexCategory.δ (0 : Fin 2))
        (SimplexCategory.δ i)).inv.app F

/-- `facePullback i α` is `(f_{δ i})^* α` after the composition identifications. -/
theorem facePullback_eq (i : Fin 3)
    {F : SheafOfModules.{w} (componentRingedSite C J O ⦋0⦌).structureSheaf}
    (α : (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullback.obj F ≅
      (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullback.obj F) :
    facePullback C J O i α =
      (ringedModulePullbackCompIso C J O (SimplexCategory.δ (1 : Fin 2))
          (SimplexCategory.δ i)).hom.app F ≫
        (ringedToposMap C J O (SimplexCategory.δ i)).modulePullback.map α.hom ≫
        (ringedModulePullbackCompIso C J O (SimplexCategory.δ (0 : Fin 2))
            (SimplexCategory.δ i)).inv.app F :=
  sorry

/-- `(f_{δ 1})^* α` transported to a morphism out of `(f_{δ 1 ≫ δ 2})^* F`. -/
def cocycleLeft
    {F : SheafOfModules.{w} (componentRingedSite C J O ⦋0⦌).structureSheaf}
    (α : (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullback.obj F ≅
      (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullback.obj F) :
    (ringedToposMap C J O
        (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (2 : Fin 3))).modulePullback.obj F ⟶
      (ringedToposMap C J O
        (SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3))).modulePullback.obj F :=
  (recodeModulePullback C J O
        (SimplexCategory.δ_comp_δ_self (i := (1 : Fin 2))).symm).hom.app F ≫
    facePullback C J O 1 α

/-- `(f_{δ 0})^* α ∘ (f_{δ 2})^* α` after the `δ_comp_δ` identifications on `C_2`. -/
def cocycleRight
    {F : SheafOfModules.{w} (componentRingedSite C J O ⦋0⦌).structureSheaf}
    (α : (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullback.obj F ≅
      (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullback.obj F) :
    (ringedToposMap C J O
        (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (2 : Fin 3))).modulePullback.obj F ⟶
      (ringedToposMap C J O
        (SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3))).modulePullback.obj F :=
  facePullback C J O 2 α ≫
    (recodeModulePullback C J O
        (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2))
          (Fin.zero_le _))).hom.app F ≫
    facePullback C J O 0 α ≫
    (recodeModulePullback C J O
        (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (0 : Fin 2))
          le_rfl).symm).hom.app F

/-- `cocycleLeft` is `(f_{δ 1})^* α` after recoding along `δ_comp_δ_self`. -/
theorem cocycleLeft_eq
    {F : SheafOfModules.{w} (componentRingedSite C J O ⦋0⦌).structureSheaf}
    (α : (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullback.obj F ≅
      (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullback.obj F) :
    cocycleLeft C J O α =
      (recodeModulePullback C J O
          (SimplexCategory.δ_comp_δ_self (i := (1 : Fin 2))).symm).hom.app F ≫
        facePullback C J O 1 α :=
  sorry

/-- `cocycleRight` is `(f_{δ 0})^* α ∘ (f_{δ 2})^* α` after the `δ_comp_δ` identifications. -/
theorem cocycleRight_eq
    {F : SheafOfModules.{w} (componentRingedSite C J O ⦋0⦌).structureSheaf}
    (α : (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullback.obj F ≅
      (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullback.obj F) :
    cocycleRight C J O α =
      facePullback C J O 2 α ≫
        (recodeModulePullback C J O
            (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2))
              (Fin.zero_le _))).hom.app F ≫
        facePullback C J O 0 α ≫
        (recodeModulePullback C J O
            (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (0 : Fin 2))
              le_rfl).symm).hom.app F :=
  sorry

/-- A pair `(F, α)` with `F` an `O_0`-module and
`α : (f_{δ 1})^* F ≅ (f_{δ 0})^* F` an isomorphism of `O_1`-modules satisfying the `O_2`
cocycle `(f_{δ 1})^* α = (f_{δ 0})^* α ∘ (f_{δ 2})^* α`. -/
def FaceDescentData :=
  { D : (Σ F : SheafOfModules.{w} (componentRingedSite C J O ⦋0⦌).structureSheaf,
      (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullback.obj F ≅
        (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullback.obj F) //
    cocycleLeft C J O D.2 = cocycleRight C J O D.2 }

namespace FaceDescentData

variable {C J O}

/-- The underlying degree-zero module of a face-descent pair. -/
def module (D : FaceDescentData C J O) :
    SheafOfModules.{w} (componentRingedSite C J O ⦋0⦌).structureSheaf :=
  D.val.1

/-- The isomorphism between the two coface pullbacks of a face-descent pair. -/
def iso (D : FaceDescentData C J O) :
    (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullback.obj D.module ≅
      (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullback.obj D.module :=
  D.val.2

end FaceDescentData

/-- The category on specified face-descent pairs induced by their degree-zero modules. -/
abbrev FaceDescentBase :=
  InducedCategory (SheafOfModules.{w} (componentRingedSite C J O ⦋0⦌).structureSheaf)
    (FaceDescentData.module (C := C) (J := J) (O := O))

/-- A map between the underlying modules commutes with the specified coface isomorphisms. -/
def faceDescentMorphismProperty : MorphismProperty (FaceDescentBase C J O) :=
  fun D E f ↦
    (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullback.map f.hom ≫
        (FaceDescentData.iso E).hom =
      (FaceDescentData.iso D).hom ≫
        (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullback.map f.hom

namespace FaceDescent

variable {C J O}

/-- The identity module map commutes with the coface isomorphism. -/
theorem hom_id_comm (D : FaceDescentData C J O) :
    (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullback.map (𝟙 D.module) ≫
        D.iso.hom =
      D.iso.hom ≫
        (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullback.map (𝟙 D.module) :=
  sorry

/-- The composite of commuting module maps commutes with the coface isomorphisms. -/
theorem hom_comp_comm {D E F : FaceDescentData C J O}
    (f : D.module ⟶ E.module) (g : E.module ⟶ F.module)
    (hf :
      (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullback.map f ≫ E.iso.hom =
        D.iso.hom ≫
          (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullback.map f)
    (hg :
      (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullback.map g ≫ F.iso.hom =
        E.iso.hom ≫
          (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullback.map g) :
    (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullback.map
        (f ≫ g) ≫ F.iso.hom =
      D.iso.hom ≫
        (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullback.map
          (f ≫ g) :=
  sorry

end FaceDescent

/-- Commuting with the coface isomorphisms is preserved by identities and composition. -/
instance faceDescentMorphismProperty_isMultiplicative :
    (faceDescentMorphismProperty C J O).IsMultiplicative where
  id_mem D := FaceDescent.hom_id_comm D
  comp_mem f g hf hg := FaceDescent.hom_comp_comm f.hom g.hom hf hg

/-- The category of specified face-descent pairs and module maps commuting with their
coface isomorphisms. -/
abbrev FaceDescent :=
  InducedWideCategory (FaceDescentBase C J O) (fun D ↦ D)
    (faceDescentMorphismProperty C J O)

namespace FaceDescent

variable {C J O}

/-- The underlying degree-zero module of a face-descent pair. -/
def module (D : FaceDescent C J O) :
    SheafOfModules.{w} (componentRingedSite C J O ⦋0⦌).structureSheaf :=
  FaceDescentData.module D

/-- The isomorphism between the two coface pullbacks of a face-descent pair. -/
def iso (D : FaceDescent C J O) :
    (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullback.obj D.module ≅
      (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullback.obj D.module :=
  FaceDescentData.iso D

/-- Build face-descent data from an `O_0`-module, a coface isomorphism of `O_1`-modules, and
the cocycle proof. -/
def ofIso (F : SheafOfModules.{w} (componentRingedSite C J O ⦋0⦌).structureSheaf)
    (α : (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullback.obj F ≅
      (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullback.obj F)
    (hcocycle : cocycleLeft C J O α = cocycleRight C J O α) :
    FaceDescent C J O :=
  ⟨⟨F, α⟩, hcocycle⟩

/-- The defining cocycle of a face-descent pair. -/
theorem spec (D : FaceDescent C J O) :
    cocycleLeft C J O D.iso = cocycleRight C J O D.iso :=
  sorry

/-- A morphism of face-descent pairs is a map of the underlying `O_0`-modules commuting
with `α`. -/
abbrev Hom (D E : FaceDescent C J O) := D ⟶ E

/-- The underlying module map of a face-descent morphism. -/
def Hom.hom {D E : FaceDescent C J O} (f : Hom D E) : D.module ⟶ E.module :=
  InducedCategory.Hom.hom (InducedWideCategory.Hom.hom f)

/-- A face-descent morphism commutes with the coface isomorphisms. -/
theorem Hom.comm {D E : FaceDescent C J O} (f : Hom D E) :
    (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullback.map f.hom ≫ E.iso.hom =
      D.iso.hom ≫
        (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullback.map f.hom :=
  f.property

/-- Build a morphism of face-descent pairs from an `O_0`-module map commuting with `α`. -/
def homMk {D E : FaceDescent C J O} (f : D.module ⟶ E.module)
    (comm :
      (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullback.map f ≫ E.iso.hom =
        D.iso.hom ≫
          (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullback.map f) :
    Hom D E :=
  ⟨InducedCategory.homMk f, comm⟩

/-- The identity morphism of face-descent pairs. -/
def Hom.id (D : FaceDescent C J O) : Hom D D :=
  𝟙 D

/-- Composition of morphisms of face-descent pairs. -/
def Hom.comp {D E F : FaceDescent C J O} (f : Hom D E) (g : Hom E F) : Hom D F :=
  f ≫ g

/-- The underlying `O_0`-module morphism of `homMk f comm` is `f`. -/
theorem homMk_hom {D E : FaceDescent C J O} (f : D.module ⟶ E.module)
    (comm :
      (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullback.map f ≫ E.iso.hom =
        D.iso.hom ≫
          (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullback.map f) :
    (homMk f comm).hom = f :=
  sorry

/-- Composing with the identity on the source leaves a face-descent morphism unchanged. -/
theorem Hom.id_comp {D E : FaceDescent C J O} (f : Hom D E) :
    Hom.comp (Hom.id D) f = f :=
  sorry

/-- Composing with the identity on the target leaves a face-descent morphism unchanged. -/
theorem Hom.comp_id {D E : FaceDescent C J O} (f : Hom D E) :
    Hom.comp f (Hom.id E) = f :=
  sorry

/-- Composition of face-descent morphisms is associative. -/
theorem Hom.assoc {D E F G : FaceDescent C J O}
    (f : Hom D E) (g : Hom E F) (h : Hom F G) :
    Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h) :=
  sorry

/-- The category of pairs `(F, α)` of an `O_0`-module and a coface isomorphism of
`O_1`-modules satisfying the `O_2` cocycle. -/
@[reducible] def category : Category (FaceDescent C J O) :=
  inferInstance

/-- The reconstructed comparison `G(φ) : (f_φ)^* G_n ⟶ G_m` attached to a pair `(F, α)`. -/
def transitionOf {n m : SimplexCategory} (φ : n ⟶ m) (D : FaceDescent C J O) :
    (ringedToposMap C J O φ).modulePullback.obj
        ((ringedToposMap C J O (vertexOp n)).modulePullback.obj D.module) ⟶
      (ringedToposMap C J O (vertexOp m)).modulePullback.obj D.module :=
  (ringedModulePullbackCompIso C J O (vertexOp n) φ).inv.app D.module ≫
    (recodeModulePullback C J O
        (SimplexCategory.Hom.ext_zero_left (vertexOp n ≫ φ)
          (SimplexCategory.δ (1 : Fin 2) ≫ edgeOp φ))).hom.app D.module ≫
    (ringedModulePullbackCompIso C J O (SimplexCategory.δ (1 : Fin 2))
        (edgeOp φ)).hom.app D.module ≫
    (ringedToposMap C J O (edgeOp φ)).modulePullback.map D.iso.hom ≫
    (ringedModulePullbackCompIso C J O (SimplexCategory.δ (0 : Fin 2))
        (edgeOp φ)).inv.app D.module ≫
    (recodeModulePullback C J O
        (SimplexCategory.Hom.ext_zero_left
          (SimplexCategory.δ (0 : Fin 2) ≫ edgeOp φ) (vertexOp m))).hom.app
      D.module

/-- `transitionOf φ D` is the source diagram for `G(φ)`, obtained by recoding along
`τ^n_n ≫ φ = τ^m_{φ(n)}` and applying `(f_{τ^m_{φ(n)m}})^* α`. -/
theorem transitionOf_eq {n m : SimplexCategory} (φ : n ⟶ m) (D : FaceDescent C J O) :
    transitionOf φ D =
      (ringedModulePullbackCompIso C J O (vertexOp n) φ).inv.app D.module ≫
        (recodeModulePullback C J O
            (SimplexCategory.Hom.ext_zero_left (vertexOp n ≫ φ)
              (SimplexCategory.δ (1 : Fin 2) ≫ edgeOp φ))).hom.app D.module ≫
        (ringedModulePullbackCompIso C J O (SimplexCategory.δ (1 : Fin 2))
            (edgeOp φ)).hom.app D.module ≫
        (ringedToposMap C J O (edgeOp φ)).modulePullback.map D.iso.hom ≫
        (ringedModulePullbackCompIso C J O (SimplexCategory.δ (0 : Fin 2))
            (edgeOp φ)).inv.app D.module ≫
        (recodeModulePullback C J O
            (SimplexCategory.Hom.ext_zero_left
              (SimplexCategory.δ (0 : Fin 2) ≫ edgeOp φ)
              (vertexOp m))).hom.app D.module :=
  sorry

/-- The identity morphism of face-descent pairs is the identity on the underlying module. -/
theorem Hom.id_hom (D : FaceDescent C J O) : (Hom.id D).hom = 𝟙 D.module :=
  sorry

/-- Composition of face-descent pairs is composition of the underlying module morphisms. -/
theorem Hom.comp_hom {D E F : FaceDescent C J O} (f : Hom D E) (g : Hom E F) :
    (Hom.comp f g).hom = f.hom ≫ g.hom :=
  sorry

end FaceDescent

end CategoryTheory.SimplicialSites.Module
