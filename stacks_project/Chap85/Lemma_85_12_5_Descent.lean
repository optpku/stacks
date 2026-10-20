/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Equivalence
public import stacks_project.Chap85.Definition_85_12_1_Cartesian
public import stacks_project.Chap85.Lemma_85_12_4_Descent

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

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instMorphismDiagram : IsMorphismDiagram C J]
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
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
structure FaceDescent where
  /-- The `O_0`-module `F`. -/
  module : SheafOfModules.{w} (componentRingedSite C J O ⦋0⦌).structureSheaf
  /-- The isomorphism `α : (f_{δ 1})^* F ≅ (f_{δ 0})^* F` of `O_1`-modules. -/
  iso :
    (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullback.obj module ≅
      (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullback.obj module
  /-- The cocycle `(f_{δ 1})^* α = (f_{δ 0})^* α ∘ (f_{δ 2})^* α` as `O_2`-module maps. -/
  cocycle : cocycleLeft C J O iso = cocycleRight C J O iso

namespace FaceDescent

variable {C J O}

/-- Build face-descent data from an `O_0`-module, a coface isomorphism of `O_1`-modules, and
the cocycle proof. -/
def ofIso (F : SheafOfModules.{w} (componentRingedSite C J O ⦋0⦌).structureSheaf)
    (α : (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullback.obj F ≅
      (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullback.obj F)
    (hcocycle : cocycleLeft C J O α = cocycleRight C J O α) :
    FaceDescent C J O where
  module := F
  iso := α
  cocycle := hcocycle

/-- The defining cocycle of a face-descent pair. -/
theorem spec (D : FaceDescent C J O) :
    cocycleLeft C J O D.iso = cocycleRight C J O D.iso :=
  sorry

/-- A morphism of face-descent pairs is a map of the underlying `O_0`-modules commuting
with `α`. -/
structure Hom (D E : FaceDescent C J O) where
  /-- The underlying morphism of `O_0`-modules. -/
  hom : D.module ⟶ E.module
  /-- Commutation with the coface isomorphisms on `C_1`. -/
  comm :
    (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullback.map hom ≫ E.iso.hom =
      D.iso.hom ≫
        (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullback.map hom

/-- Build a morphism of face-descent pairs from an `O_0`-module map commuting with `α`. -/
def homMk {D E : FaceDescent C J O} (f : D.module ⟶ E.module)
    (comm :
      (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullback.map f ≫ E.iso.hom =
        D.iso.hom ≫
          (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullback.map f) :
    Hom D E where
  hom := f
  comm := comm

/-- The identity morphism of face-descent pairs. -/
def Hom.id (D : FaceDescent C J O) : Hom D D :=
  homMk (𝟙 D.module) sorry

/-- Composition of morphisms of face-descent pairs. -/
def Hom.comp {D E F : FaceDescent C J O} (f : Hom D E) (g : Hom E F) : Hom D F :=
  homMk (f.hom ≫ g.hom) sorry

/-- The underlying `O_0`-module morphism of `homMk f comm` is `f`. -/
theorem homMk_hom {D E : FaceDescent C J O} (f : D.module ⟶ E.module)
    (comm :
      (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2))).modulePullback.map f ≫ E.iso.hom =
        D.iso.hom ≫
          (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2))).modulePullback.map f) :
    (homMk f comm).hom = f :=
  sorry

/-- The category of pairs `(F, α)` of an `O_0`-module and a coface isomorphism of
`O_1`-modules satisfying the `O_2` cocycle. -/
instance category : Category (FaceDescent C J O) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The reconstructed comparison `G(φ) : (f_φ)^* G_n ⟶ G_m` attached to a pair `(F, α)`. -/
def transitionOf {n m : SimplexCategory} (φ : n ⟶ m) (D : FaceDescent C J O) :
    (ringedToposMap C J O φ).modulePullback.obj
        ((ringedToposMap C J O (Sheaf.vertexOp n)).modulePullback.obj D.module) ⟶
      (ringedToposMap C J O (Sheaf.vertexOp m)).modulePullback.obj D.module :=
  (ringedModulePullbackCompIso C J O (Sheaf.vertexOp n) φ).inv.app D.module ≫
    (recodeModulePullback C J O
        (SimplexCategory.Hom.ext_zero_left (Sheaf.vertexOp n ≫ φ)
          (SimplexCategory.δ (1 : Fin 2) ≫ Sheaf.edgeOp φ))).hom.app D.module ≫
    (ringedModulePullbackCompIso C J O (SimplexCategory.δ (1 : Fin 2))
        (Sheaf.edgeOp φ)).hom.app D.module ≫
    (ringedToposMap C J O (Sheaf.edgeOp φ)).modulePullback.map D.iso.hom ≫
    (ringedModulePullbackCompIso C J O (SimplexCategory.δ (0 : Fin 2))
        (Sheaf.edgeOp φ)).inv.app D.module ≫
    (recodeModulePullback C J O
        (SimplexCategory.Hom.ext_zero_left
          (SimplexCategory.δ (0 : Fin 2) ≫ Sheaf.edgeOp φ) (Sheaf.vertexOp m))).hom.app
      D.module

/-- `transitionOf φ D` is the source diagram for `G(φ)`, obtained by recoding along
`τ^n_n ≫ φ = τ^m_{φ(n)}` and applying `(f_{τ^m_{φ(n)m}})^* α`. -/
theorem transitionOf_eq {n m : SimplexCategory} (φ : n ⟶ m) (D : FaceDescent C J O) :
    transitionOf φ D =
      (ringedModulePullbackCompIso C J O (Sheaf.vertexOp n) φ).inv.app D.module ≫
        (recodeModulePullback C J O
            (SimplexCategory.Hom.ext_zero_left (Sheaf.vertexOp n ≫ φ)
              (SimplexCategory.δ (1 : Fin 2) ≫ Sheaf.edgeOp φ))).hom.app D.module ≫
        (ringedModulePullbackCompIso C J O (SimplexCategory.δ (1 : Fin 2))
            (Sheaf.edgeOp φ)).hom.app D.module ≫
        (ringedToposMap C J O (Sheaf.edgeOp φ)).modulePullback.map D.iso.hom ≫
        (ringedModulePullbackCompIso C J O (SimplexCategory.δ (0 : Fin 2))
            (Sheaf.edgeOp φ)).inv.app D.module ≫
        (recodeModulePullback C J O
            (SimplexCategory.Hom.ext_zero_left
              (SimplexCategory.δ (0 : Fin 2) ≫ Sheaf.edgeOp φ)
              (Sheaf.vertexOp m))).hom.app D.module :=
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
