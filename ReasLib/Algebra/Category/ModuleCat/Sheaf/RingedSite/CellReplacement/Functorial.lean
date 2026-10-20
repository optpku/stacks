module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CellReplacement

/-!
# Functorial maps of the displayed cell resolution

A map of input complexes sends each actual cell pair `(x, y)` to the corresponding pair of
images. Native free-module maps, biproduct maps and colimit maps then give all the resolution
maps. No compatible map is chosen from an existence or lifting theorem.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w uC vC

namespace PresheafOfModules.CellReplacement

variable {C : Type uC} [Category.{vC} C] {R : Cᵒᵖ ⥤ RingCat.{w}}
variable {F F' K K' : Complex R} {φ : F ⟶ K} {ψ : F' ⟶ K'}

/-- The image of a cell still has its specified boundary after a commuting augmentation square. -/
theorem cellMap_dx (f : F ⟶ F') (g : K ⟶ K') (comm : φ ≫ g = f ≫ ψ)
    (n : ℤ) (U : Cᵒᵖ) (c : Cell φ n U) :
    (K'.d n (n + 1)).app U ((g.f n).app U c.x) =
      (ψ.f (n + 1)).app U ((f.f (n + 1)).app U c.y) := sorry

/-- A complex map carries the old cell's cycle coordinate to a cycle. -/
theorem cellMap_dy (f : F ⟶ F') (n : ℤ) (U : Cᵒᵖ) (c : Cell φ n U) :
    (F'.d (n + 1) ((n + 1) + 1)).app U ((f.f (n + 1)).app U c.y) = 0 := sorry

/-- The actual coordinate map on local cells. -/
def cellMap (f : F ⟶ F') (g : K ⟶ K') (comm : φ ≫ g = f ≫ ψ)
    (n : ℤ) (U : Cᵒᵖ) (c : Cell φ n U) : Cell ψ n U where
  x := (g.f n).app U c.x
  y := (f.f (n + 1)).app U c.y
  dx := cellMap_dx f g comm n U c
  dy := cellMap_dy f n U c

/-- Coordinate maps commute with the original presheaf restrictions. -/
def cellsMap (f : F ⟶ F') (g : K ⟶ K') (comm : φ ≫ g = f ≫ ψ) (n : ℤ) :
    cells φ n ⟶ cells ψ n where
  app U := ↾cellMap f g comm n U
  naturality := sorry

/-- Extend the specified coordinate map on free generators. -/
def freeCellsMap (f : F ⟶ F') (g : K ⟶ K') (comm : φ ≫ g = f ≫ ψ) (n : ℤ) :
    freeCells φ n ⟶ freeCells ψ n :=
  (PresheafOfModules.free R).map (cellsMap f g comm n)

/-- The map on the enlarged term is the actual map on the two biproduct summands. -/
def nextTermMap (f : F ⟶ F') (g : K ⟶ K') (comm : φ ≫ g = f ≫ ψ) (n : ℤ) :
    nextTerm φ n ⟶ nextTerm ψ n :=
  biprod.map (f.f n) (freeCellsMap f g comm n)

/-- These biproduct maps commute with the differential that sends new generators into old cells. -/
theorem nextMap_comm (f : F ⟶ F') (g : K ⟶ K') (comm : φ ≫ g = f ≫ ψ)
    (i j : ℤ) :
    (nextComplex φ).d i j ≫ nextTermMap f g comm j =
      nextTermMap f g comm i ≫ (nextComplex ψ).d i j := sorry

/-- The actual map of attached-cell complexes. -/
def nextMap (f : F ⟶ F') (g : K ⟶ K') (comm : φ ≫ g = f ≫ ψ) :
    nextComplex φ ⟶ nextComplex ψ where
  f := nextTermMap f g comm
  comm' := fun i j _ ↦ (nextMap_comm f g comm i j).symm

/-- Cell maps retain the specified augmentation square. -/
theorem nextMap_augmentation (f : F ⟶ F') (g : K ⟶ K') (comm : φ ≫ g = f ≫ ψ) :
    nextMap f g comm ≫ nextAugmentation ψ = nextAugmentation φ ≫ g := sorry

/-- A map of stages stores its actual complex map and augmentation square. -/
structure StageMap (g : K ⟶ K') (s : Stage K) (t : Stage K') where
  hom : s.complex ⟶ t.complex
  comm : hom ≫ t.augmentation = s.augmentation ≫ g

/-- The next stage map is induced by the actual old-stage and input maps. -/
def StageMap.next {g : K ⟶ K'} {s : Stage K} {t : Stage K'} (f : StageMap g s t) :
    StageMap g s.next t.next where
  hom := nextMap f.hom g f.comm.symm
  comm := nextMap_augmentation f.hom g f.comm.symm

/-- The zero seed stage carries the zero map to the corresponding zero seed. -/
def seedMap (g : K ⟶ K') : StageMap g (seed K) (seed K') where
  hom := 0
  comm := by simp [seed]

/-- Maps of all stages are defined recursively, in step with the displayed tower. -/
def stageMorphism (g : K ⟶ K') : (n : ℕ) → StageMap g (stage K n) (stage K' n)
  | 0 => seedMap g
  | n + 1 => (stageMorphism g n).next

/-- The actual stage maps commute with old-summand transition inclusions. -/
theorem stageMorphism_transition (g : K ⟶ K') (n : ℕ) :
    transition K n ≫ (stageMorphism g (n + 1)).hom =
      (stageMorphism g n).hom ≫ transition K' n := sorry

/-- The recursive stage maps commute with every map of the attaching diagrams. -/
theorem diagramMap_naturality (g : K ⟶ K') (i j : ℕ) (a : i ⟶ j) :
    (diagram K).map a ≫ (stageMorphism g j).hom =
      (stageMorphism g i).hom ≫ (diagram K').map a := sorry

/-- The actual natural transformation between the two attaching diagrams. -/
def diagramMap (g : K ⟶ K') : diagram K ⟶ diagram K' where
  app n := (stageMorphism g n).hom
  naturality := diagramMap_naturality g

/-- The replacement map is induced by the original stage maps on the colimit. -/
def replacementMap (g : K ⟶ K') : replacement K ⟶ replacement K' :=
  colim.map (diagramMap g)

/-- The prescribed augmentation is natural in the input complex. -/
theorem replacementMap_augmentation (g : K ⟶ K') :
    replacementMap g ≫ augmentation K' = augmentation K ≫ g := sorry

/-- The displayed presheaf cell replacement acts on maps through their actual coordinates. -/
def functor : Complex R ⥤ Complex R where
  obj := replacement
  map := replacementMap
  map_id := sorry
  map_comp := sorry

/-- The specified original augmentation, as a natural transformation. -/
def augmentationNatTrans : functor (R := R) ⟶ 𝟭 (Complex R) where
  app := augmentation
  naturality := fun _ _ f ↦ replacementMap_augmentation f

end PresheafOfModules.CellReplacement

namespace SheafOfModules.CellReplacement

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}
variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {K L : CochainComplex (SheafOfModules.{w} R) ℤ}

/-- The original map of underlying presheaf complexes. -/
def underlyingMap (f : K ⟶ L) : underlying K ⟶ underlying L :=
  ((SheafOfModules.forget R).mapHomologicalComplex (ComplexShape.up ℤ)).map f

/-- Its actual free-cell colimit map. -/
def presheafMap (f : K ⟶ L) : presheafModel K ⟶ presheafModel L :=
  PresheafOfModules.CellReplacement.replacementMap (underlyingMap f)

/-- Sheafification of the specified replacement map in each degree. -/
def modelTermMap (f : K ⟶ L) (n : ℤ) : modelTerm K n ⟶ modelTerm L n :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map ((presheafMap f).f n)

/-- The sheafified term maps commute with the actual model differentials. -/
theorem modelMap_comm (f : K ⟶ L) (i j : ℤ) :
    (model K).d i j ≫ modelTermMap f j = modelTermMap f i ≫ (model L).d i j := sorry

/-- The actual map between global sheaf cell models. -/
def modelMap (f : K ⟶ L) : model K ⟶ model L where
  f := modelTermMap f
  comm' := fun i j _ ↦ (modelMap_comm f i j).symm

/-- The sheafified model maps retain the original augmentation square. -/
theorem modelMap_augmentation (f : K ⟶ L) :
    modelMap f ≫ augmentation L = augmentation K ≫ f := sorry

/-- The concrete sheaf cell replacement functor. -/
def functor : CochainComplex (SheafOfModules.{w} R) ℤ ⥤
    CochainComplex (SheafOfModules.{w} R) ℤ where
  obj := model
  map := modelMap
  map_id := sorry
  map_comp := sorry

/-- The original augmentation, as a natural transformation on complexes. -/
def augmentationNatTrans : functor (R := R) ⟶ 𝟭 (CochainComplex (SheafOfModules.{w} R) ℤ) where
  app := augmentation
  naturality := fun _ _ f ↦ modelMap_augmentation f

end SheafOfModules.CellReplacement
