module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Tactic.CrossRefAttribute

/-!
# A displayed cell replacement of an unbounded complex of modules

Given a map of complexes `φ : F ⟶ K`, attach in degree `n` the free module on the pairs `(x, y)`
with `x ∈ K^n`, `y ∈ F^{n+1}`, `dx = φ(y)` and `dy = 0`. The new differential sends the
generator to `y` and the new augmentation sends it to `x`. Starting from zero and taking the
sequential colimit gives an explicit semi-free complex with its specified augmentation to the
original (arbitrary, unbounded) input. No complex, map or generator is selected from a
resolution-existence theorem.

The free modules have coefficients `Shrink.{v} R`, so the construction lives in
`ModuleCat.{v} R` whenever `R` is `v`-small; this holds automatically when `v` is at least the
universe of `R`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

noncomputable section

universe v u

namespace ModuleCat.CellReplacement

variable {R : Type u} [Ring R] [Small.{v} R]

/-- Unbounded cochain complexes of `R`-modules. -/
abbrev Complex (R : Type u) [Ring R] := CochainComplex (ModuleCat.{v} R) ℤ

variable {F K : Complex.{v} R} (φ : F ⟶ K)

/-- The literal attaching data: a target element together with a source cycle bounding it. -/
structure Cell (n : ℤ) : Type v where
  /-- The coordinate sent to the original target by the augmentation. -/
  x : K.X n
  /-- The coordinate hit by the differential of the new generator. -/
  y : F.X (n + 1)
  dx : (K.d n (n + 1)).hom x = (φ.f (n + 1)).hom y
  dy : (F.d (n + 1) ((n + 1) + 1)).hom y = 0

/-- The free `R`-module on the cells, with `v`-small coefficients. -/
def freeCells (n : ℤ) : ModuleCat.{v} R := ModuleCat.of R (Cell φ n →₀ Shrink.{v} R)

/-- The standard basis of the free module on the cells. -/
def cellBasis (n : ℤ) : Module.Basis (Cell φ n) R (freeCells φ n) :=
  ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv R R)⟩

/-- Send each free generator to its target coordinate `x`. -/
def evaluateX (n : ℤ) : freeCells φ n ⟶ K.X n :=
  ModuleCat.ofHom ((cellBasis φ n).constr ℕ fun c => c.x)

/-- Send each free generator to its boundary coordinate `y`. -/
def evaluateY (n : ℤ) : freeCells φ n ⟶ F.X (n + 1) :=
  ModuleCat.ofHom ((cellBasis φ n).constr ℕ fun c => c.y)

/-- The term of the attached-cell complex: old term plus the new free generators. -/
def nextTerm (n : ℤ) : ModuleCat.{v} R := F.X n ⊞ freeCells φ n

/-- The attached-cell differential: old differential on the first summand, the specified `y`
on the new generators, and no new-component contribution. -/
def nextDifferential (n : ℤ) : nextTerm φ n ⟶ nextTerm φ (n + 1) :=
  biprod.desc (F.d n (n + 1) ≫ biprod.inl) (evaluateY φ n ≫ biprod.inl)

theorem nextDifferential_sq (n : ℤ) :
    nextDifferential φ n ≫ nextDifferential φ (n + 1) = 0 := sorry

/-- The complex obtained by attaching all cells of `φ`. -/
def nextComplex : Complex.{v} R :=
  CochainComplex.of (nextTerm φ) (nextDifferential φ) (nextDifferential_sq φ)

/-- The augmentation of the attached-cell complex: `φ` on old terms and `x` on new generators. -/
def nextAugmentation : nextComplex φ ⟶ K where
  f n := biprod.desc (φ.f n) (evaluateX φ n)
  comm' := sorry

/-- The old complex is a subcomplex of the attached-cell complex. -/
def inclusion : F ⟶ nextComplex φ where
  f _ := biprod.inl
  comm' := sorry

theorem inclusion_augmentation : inclusion φ ≫ nextAugmentation φ = φ := by
  ext n : 1
  exact biprod.inl_desc (φ.f n) (evaluateX φ n)

/-- The augmentation sends every new generator to its prescribed `x`. -/
theorem augmentation_generator (n : ℤ) (c : Cell φ n) :
    ((biprod.inr : freeCells φ n ⟶ nextTerm φ n) ≫ (nextAugmentation φ).f n).hom
      (cellBasis φ n c) = c.x := sorry

/-- A stage stores its actual complex and its actual map to the original `K`. -/
structure Stage (K : Complex.{v} R) where
  /-- The stage complex. -/
  complex : Complex.{v} R
  /-- The stage augmentation. -/
  augmentation : complex ⟶ K

/-- Attach all cells of the current augmentation. -/
def Stage.next (s : Stage K) : Stage K :=
  ⟨nextComplex s.augmentation, nextAugmentation s.augmentation⟩

/-- The zero seed stage. -/
def seed (K : Complex.{v} R) : Stage K := ⟨0, 0⟩

/-- The recursive attaching tower. -/
def stage (K : Complex.{v} R) : ℕ → Stage K
  | 0 => seed K
  | n + 1 => (stage K n).next

/-- The old-summand inclusion between consecutive stages. -/
def transition (K : Complex.{v} R) (n : ℕ) :
    (stage K n).complex ⟶ (stage K (n + 1)).complex :=
  inclusion (stage K n).augmentation

/-- The sequential attaching diagram. -/
def diagram (K : Complex.{v} R) : ℕ ⥤ Complex.{v} R := Functor.ofSequence (transition K)

/-- The explicit colimit of the displayed attaching tower. -/
def replacement (K : Complex.{v} R) : Complex.{v} R := colimit (diagram K)

/-- The stage augmentations form a cocone over the attaching diagram. -/
def augmentationCocone (K : Complex.{v} R) : Cocone (diagram K) where
  pt := K
  ι := NatTrans.ofSequence (fun n => (stage K n).augmentation) (by
    intro n
    exact (congrArg (fun f => f ≫ (stage K (n + 1)).augmentation)
      (Functor.ofSequence_map_homOfLE_succ (transition K) n)).trans
        ((inclusion_augmentation (stage K n).augmentation).trans (Category.comp_id _).symm))

/-- The canonical comparison to the original input, not an arbitrary quasi-isomorphism. -/
def augmentation (K : Complex.{v} R) : replacement K ⟶ K :=
  colimit.desc (diagram K) (augmentationCocone K)

theorem stage_augmentation (K : Complex.{v} R) (n : ℕ) :
    colimit.ι (diagram K) n ≫ augmentation K = (stage K n).augmentation :=
  colimit.ι_desc _ _

/-- Every target cycle is attached at the first stage, and every source cycle in the kernel of
the augmentation is killed by its displayed cell at the following stage; sequential colimits of
modules are exact. -/
@[stacks 064M "displayed cell augmentation is a quasi-isomorphism"]
theorem augmentation_quasiIso (K : Complex.{v} R) : QuasiIso (augmentation K) := sorry

/-- The displayed replacement is K-projective: it is the colimit of termwise split inclusions
whose quotients are complexes of free modules with zero differential. -/
@[stacks 064M "displayed cell replacement is K-projective"]
theorem replacement_isKProjective (K : Complex.{v} R) : (replacement K).IsKProjective := sorry

/-! ### Functoriality through the actual cell coordinates -/

section Functorial

variable {F' K' : Complex.{v} R} {ψ : F' ⟶ K'}

/-- The image of a cell still has its specified boundary after a commuting augmentation square. -/
theorem cellMap_dx (f : F ⟶ F') (g : K ⟶ K') (comm : φ ≫ g = f ≫ ψ) (n : ℤ) (c : Cell φ n) :
    (K'.d n (n + 1)).hom ((g.f n).hom c.x) = (ψ.f (n + 1)).hom ((f.f (n + 1)).hom c.y) := sorry

/-- A complex map carries the cycle coordinate of a cell to a cycle. -/
theorem cellMap_dy (f : F ⟶ F') (n : ℤ) (c : Cell φ n) :
    (F'.d (n + 1) ((n + 1) + 1)).hom ((f.f (n + 1)).hom c.y) = 0 := sorry

/-- The actual coordinate map on cells. -/
def cellMap (f : F ⟶ F') (g : K ⟶ K') (comm : φ ≫ g = f ≫ ψ) (n : ℤ) (c : Cell φ n) :
    Cell ψ n where
  x := (g.f n).hom c.x
  y := (f.f (n + 1)).hom c.y
  dx := cellMap_dx φ f g comm n c
  dy := cellMap_dy φ f n c

/-- Extend the coordinate map on free generators. -/
def freeCellsMap (f : F ⟶ F') (g : K ⟶ K') (comm : φ ≫ g = f ≫ ψ) (n : ℤ) :
    freeCells φ n ⟶ freeCells ψ n :=
  ModuleCat.ofHom (Finsupp.lmapDomain (Shrink.{v} R) R (cellMap φ f g comm n))

/-- The map on the enlarged term is the actual map on the two biproduct summands. -/
def nextTermMap (f : F ⟶ F') (g : K ⟶ K') (comm : φ ≫ g = f ≫ ψ) (n : ℤ) :
    nextTerm φ n ⟶ nextTerm ψ n :=
  biprod.map (f.f n) (freeCellsMap φ f g comm n)

/-- These biproduct maps commute with the attached-cell differentials. -/
theorem nextMap_comm (f : F ⟶ F') (g : K ⟶ K') (comm : φ ≫ g = f ≫ ψ) (i j : ℤ) :
    (nextComplex φ).d i j ≫ nextTermMap φ f g comm j =
      nextTermMap φ f g comm i ≫ (nextComplex ψ).d i j := sorry

/-- The actual map of attached-cell complexes. -/
def nextMap (f : F ⟶ F') (g : K ⟶ K') (comm : φ ≫ g = f ≫ ψ) :
    nextComplex φ ⟶ nextComplex ψ where
  f := nextTermMap φ f g comm
  comm' := fun i j _ ↦ (nextMap_comm φ f g comm i j).symm

/-- Cell maps retain the specified augmentation square. -/
theorem nextMap_augmentation (f : F ⟶ F') (g : K ⟶ K') (comm : φ ≫ g = f ≫ ψ) :
    nextMap φ f g comm ≫ nextAugmentation ψ = nextAugmentation φ ≫ g := sorry

end Functorial

/-- A map of stages stores its actual complex map and augmentation square. -/
structure StageMap {K K' : Complex.{v} R} (g : K ⟶ K') (s : Stage K) (t : Stage K') where
  /-- The map of stage complexes. -/
  hom : s.complex ⟶ t.complex
  comm : hom ≫ t.augmentation = s.augmentation ≫ g

variable {K K' : Complex.{v} R}

/-- The next stage map is induced by the actual old-stage and input maps. -/
def StageMap.next {g : K ⟶ K'} {s : Stage K} {t : Stage K'} (f : StageMap g s t) :
    StageMap g s.next t.next where
  hom := nextMap s.augmentation f.hom g f.comm.symm
  comm := nextMap_augmentation s.augmentation f.hom g f.comm.symm

/-- The zero seed stage carries the zero map to the corresponding zero seed. -/
def seedMap (g : K ⟶ K') : StageMap g (seed K) (seed K') where
  hom := 0
  comm := by simp [seed]

/-- Maps of all stages, defined recursively in step with the attaching tower. -/
def stageMorphism (g : K ⟶ K') : (n : ℕ) → StageMap g (stage K n) (stage K' n)
  | 0 => seedMap g
  | n + 1 => (stageMorphism g n).next

/-- The recursive stage maps commute with every map of the attaching diagrams. -/
theorem diagramMap_naturality (g : K ⟶ K') (i j : ℕ) (a : i ⟶ j) :
    (diagram K).map a ≫ (stageMorphism g j).hom =
      (stageMorphism g i).hom ≫ (diagram K').map a := sorry

/-- The actual natural transformation between the two attaching diagrams. -/
def diagramMap (g : K ⟶ K') : diagram K ⟶ diagram K' where
  app n := (stageMorphism g n).hom
  naturality := diagramMap_naturality g

/-- The replacement map is induced by the actual stage maps on the colimit. -/
def replacementMap (g : K ⟶ K') : replacement K ⟶ replacement K' :=
  colim.map (diagramMap g)

/-- The prescribed augmentation is natural in the input complex. -/
theorem replacementMap_augmentation (g : K ⟶ K') :
    replacementMap g ≫ augmentation K' = augmentation K ≫ g := sorry

variable (R) in
/-- The displayed cell replacement as an endofunctor of unbounded complexes. -/
def functor : Complex.{v} R ⥤ Complex.{v} R where
  obj := replacement
  map := replacementMap
  map_id := sorry
  map_comp := sorry

variable (R) in
/-- The specified augmentation, as a natural transformation. -/
def augmentationNatTrans : functor R ⟶ 𝟭 (Complex.{v} R) where
  app := augmentation
  naturality := fun _ _ f ↦ replacementMap_augmentation f

end ModuleCat.CellReplacement
