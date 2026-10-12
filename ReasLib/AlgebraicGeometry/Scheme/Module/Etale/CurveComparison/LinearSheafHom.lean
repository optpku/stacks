/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.SiteExtComparison
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Linear.FunctorCategory

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace ActualLinearSheafHom
variable (Y : Scheme.{u}) (R : Type (u + 1)) [CommRing R]
variable (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))

/-- Local linear morphisms on the actual slice category, with pointwise scalars. -/
def presheaf : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R where
  obj U := ModuleCat.of R ((Over.forget U.unop).op ⋙ F.obj ⟶
    (Over.forget U.unop).op ⋙ G.obj)
  map f := ModuleCat.ofHom
    { toFun := fun α ↦ Functor.whiskerLeft (Over.map f.unop).op α
      map_add' := sorry
      map_smul' := sorry }
  map_id := sorry
  map_comp := sorry

/-- Linear local morphisms glue uniquely because their target is a sheaf. -/
theorem isSheaf : Presheaf.IsSheaf Y.smallEtaleTopology (presheaf Y R F G) := sorry

/-- The linear internal-Hom sheaf, without a chosen abstract closed structure. -/
def obj : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R) :=
  ⟨presheaf Y R F G, isSheaf Y R F G⟩

/-- Functoriality in the target is pointwise postcomposition. -/
def map {G H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)} (f : G ⟶ H) :
    obj Y R F G ⟶ obj Y R F H :=
  ObjectProperty.homMk
    { app := fun U ↦ ModuleCat.ofHom
        { toFun := fun α ↦ α ≫ Functor.whiskerLeft (Over.forget U.unop).op f.hom
          map_add' := sorry
          map_smul' := sorry }
      naturality := sorry }

/-- Actual covariant linear internal Hom with fixed source. -/
def functor : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤
    Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R) where
  obj := obj Y R F
  map := map Y R F
  map_id := sorry
  map_comp := sorry

instance functor_additive : (functor Y R F).Additive := sorry

/-- A global local morphism evaluates over the unique map to the terminal etale object. -/
def sectionsToHom (α : (obj Y R F G).obj.obj (op (globalEtale Y))) : F ⟶ G :=
  ObjectProperty.homMk
    { app := fun U ↦ α.app (op (Over.mk
        ((MorphismProperty.Over.mkIdTerminal @Etale Y).from U.unop)))
      naturality := sorry }

/-- A sheaf morphism restricts to every object over the terminal etale object. -/
def homToSections (f : F ⟶ G) : (obj Y R F G).obj.obj (op (globalEtale Y)) :=
  Functor.whiskerLeft (Over.forget (globalEtale Y)).op f.hom

variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R)]

/-- Evaluation/restriction identifies sections of linear internal Hom with actual morphisms. -/
def sectionsHomIso :
    functor Y R F ⋙ AmbientAssociatedSheaf.sections (X := Y) R ⋙
      forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1} ≅
    ActualHomDerivedExt.homFunctor F :=
  NatIso.ofComponents (fun G ↦
    ({ toFun := sectionsToHom Y R F G
       invFun := homToSections Y R F G
       left_inv := sorry
       right_inv := sorry
       map_add' := sorry } :
      (obj Y R F G).obj.obj (op (globalEtale Y)) ≃+ (F ⟶ G)).toAddCommGrpIso)
    (fun _ ↦ sorry)

end ActualLinearSheafHom
