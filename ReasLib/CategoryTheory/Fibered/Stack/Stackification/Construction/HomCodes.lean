module

public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Construction.SmallHoms
public import Mathlib.CategoryTheory.Sites.Plus

/-!
# Local-arrow sections on an actual small local site

The separated stage already has original-universe Hom types. A local-arrow
representative gives a compatible family of those actual arrows after taking
the pullback covering sieve on a small local site.
-/

@[expose] public section

open CategoryTheory Opposite GrothendieckTopology
open CategoryTheory.Limits
open scoped CategoryTheory.Bicategory

noncomputable section

universe u v uX vX w

namespace CategoryTheory.Functor.StackificationConstruction

variable {C : Type u} [Category.{v} C] {X : Type uX} [Category.{vX} X]
variable (J : GrothendieckTopology C) (p : X ⥤ C) (χ : p.Cleavage)

/-- The separated cleavage retains the original lift objects, arrows and factors. -/
def separatedCleavage : (Separated.projection J p χ).Cleavage where
  lift {a V} f :=
    let l := χ.lift (x := (a : Separated J p χ).obj) f
    { source := (Separated.ofOriginal J p χ).obj l.source
      hom := (Separated.ofOriginal J p χ).map l.hom
      isStronglyCartesian :=
        @Separated.mapIsStronglyCartesian _ _ _ _ J p χ
          l.source a.obj V (p.obj a.obj) f l.hom l.isStronglyCartesian }

/-- An original object lies in the separated fibre over its actual base. -/
def separatedFiber (a : X) : (Separated.projection J p χ).Fiber (p.obj a) :=
  ⟨(Separated.ofOriginal J p χ).obj a, rfl⟩

/-- The original target's actual chosen restriction, in the separated fibre. -/
def separatedTarget (a b : X) (g : p.obj a ⟶ p.obj b) :
    (Separated.projection J p χ).Fiber (p.obj a) :=
  ⟨(Separated.ofOriginal J p χ).obj
      (χ.reindexLift g (⟨b, rfl⟩ : p.Fiber (p.obj b))).source,
    (χ.reindexLift g (⟨b, rfl⟩ : p.Fiber (p.obj b))).sourceObj⟩

/-- The separated Hom presheaf has values in the original Hom universe. -/
def separatedHom (a b : X) (g : p.obj a ⟶ p.obj b) :
    (Over (p.obj a))ᵒᵖ ⥤ Type vX :=
  (separatedCleavage J p χ).toPseudofunctor.presheafHom
    (separatedFiber J p χ a) (separatedTarget J p χ a b g)

/-- The separated lift has exactly the original lift object after its stored
fibre endpoint equality is eliminated. -/
theorem separatedReindex_obj {U V : C} (f : V ⟶ U) (x : p.Fiber U) :
    ((separatedCleavage J p χ).reindexObj f (⟨(Separated.ofOriginal J p χ).obj x.1, x.2⟩ :
      (Separated.projection J p χ).Fiber U)).1 =
      (Separated.ofOriginal J p χ).obj (χ.reindexObj f x).1 := by
  rcases x with ⟨x, rfl⟩
  rfl

/-- A local component is factored twice through actual original selected lifts,
so it becomes a section of the separated Hom presheaf. -/
def separatedSection {a b : X}
    (φ : LocalArrow J p χ ((Separated.ofOriginal J p χ).obj a)
      ((Separated.ofOriginal J p χ).obj b))
    (I : φ.cover.Arrow) : (separatedHom J p χ a b φ.base).obj (op (Over.mk I.f)) := by
  let q : Separated J p χ ⥤ C := Separated.projection J p χ
  let target := χ.reindexLift φ.base (⟨b, rfl⟩ : p.Fiber (p.obj b))
  let targetArrow : (Separated.ofOriginal J p χ).obj target.source ⟶
      (Separated.ofOriginal J p χ).obj b := (Separated.ofOriginal J p χ).map target.hom
  let targetStrong : q.IsStronglyCartesian φ.base targetArrow :=
    @Separated.mapIsStronglyCartesian _ _ _ _ J p χ
      target.source b (p.obj a) (p.obj b) φ.base target.hom target.isStronglyCartesian
  let first := @Functor.IsStronglyCartesian.map C (Separated J p χ) _ _ q
    (p.obj a) (p.obj b) ((Separated.ofOriginal J p χ).obj target.source)
    ((Separated.ofOriginal J p χ).obj b) φ.base targetArrow targetStrong
    I.Y ((Separated.ofOriginal J p χ).obj
      (sourceRestriction J p χ ((Separated.ofOriginal J p χ).obj a) I.f))
    I.f (I.f ≫ φ.base) rfl (φ.component I) (φ.isHomLift I)
  have firstLift : q.IsHomLift I.f first :=
    @Functor.IsStronglyCartesian.map_isHomLift C (Separated J p χ) _ _ q
      (p.obj a) (p.obj b) ((Separated.ofOriginal J p χ).obj target.source)
      ((Separated.ofOriginal J p χ).obj b) φ.base targetArrow targetStrong
      I.Y ((Separated.ofOriginal J p χ).obj
        (sourceRestriction J p χ ((Separated.ofOriginal J p χ).obj a) I.f))
      I.f (I.f ≫ φ.base) rfl (φ.component I) (φ.isHomLift I)
  let restricted := χ.reindexLift I.f (⟨target.source, target.sourceObj⟩ : p.Fiber (p.obj a))
  let restrictedArrow : (Separated.ofOriginal J p χ).obj restricted.source ⟶
      (Separated.ofOriginal J p χ).obj target.source :=
    (Separated.ofOriginal J p χ).map restricted.hom
  let restrictedStrong : q.IsStronglyCartesian I.f restrictedArrow :=
    @Separated.mapIsStronglyCartesian _ _ _ _ J p χ
      restricted.source target.source I.Y (p.obj a)
      I.f restricted.hom restricted.isStronglyCartesian
  let second := @Functor.IsStronglyCartesian.map C (Separated J p χ) _ _ q
    I.Y (p.obj a) ((Separated.ofOriginal J p χ).obj restricted.source)
    ((Separated.ofOriginal J p χ).obj target.source) I.f restrictedArrow restrictedStrong
    I.Y ((Separated.ofOriginal J p χ).obj
      (sourceRestriction J p χ ((Separated.ofOriginal J p χ).obj a) I.f))
    (𝟙 I.Y) I.f (Category.id_comp I.f).symm first firstLift
  have secondLift : q.IsHomLift (𝟙 I.Y) second :=
    @Functor.IsStronglyCartesian.map_isHomLift C (Separated J p χ) _ _ q
      I.Y (p.obj a) ((Separated.ofOriginal J p χ).obj restricted.source)
      ((Separated.ofOriginal J p χ).obj target.source) I.f restrictedArrow restrictedStrong
      I.Y ((Separated.ofOriginal J p χ).obj
        (sourceRestriction J p χ ((Separated.ofOriginal J p χ).obj a) I.f))
      (𝟙 I.Y) I.f (Category.id_comp I.f).symm first firstLift
  exact ⟨eqToHom (separatedReindex_obj J p χ I.f (⟨a, rfl⟩ : p.Fiber (p.obj a))) ≫
    second ≫ eqToHom (separatedReindex_obj J p χ I.f
      (⟨target.source, target.sourceObj⟩ : p.Fiber (p.obj a))).symm, by sorry⟩

variable {D : Type vX} [Category.{vX} D] (K : GrothendieckTopology D)
variable {a b : X} (G : D ⥤ Over (p.obj a)) [G.IsCocontinuous K (J.over (p.obj a))]

/-- Pull back the original representative cover along the actual local-site
functor. The given cocontinuity witness supplies its original covering law. -/
def codeCover (φ : LocalArrow J p χ ((Separated.ofOriginal J p χ).obj a)
    ((Separated.ofOriginal J p χ).obj b)) (d : D) :
    K.Cover d :=
  ⟨((Sieve.overEquiv (G.obj d)).symm
      (φ.cover.pullback (G.obj d).hom : Sieve (G.obj d).left)).functorPullback G,
    G.cover_lift K (J.over (p.obj a))
      (J.overEquiv_symm_mem_over (G.obj d) _ (φ.cover.pullback (G.obj d).hom).2)⟩

/-- The actual slice-map equation identifies the original covering arrow. -/
theorem codeCover_member (φ : LocalArrow J p χ ((Separated.ofOriginal J p χ).obj a)
    ((Separated.ofOriginal J p χ).obj b))
    (d : D) (I : (codeCover J p χ K G φ d).Arrow) :
    φ.cover (G.obj I.Y).hom := by
  have member : φ.cover ((G.map I.f).left ≫ (G.obj d).hom) := I.hf
  exact (Over.w (G.map I.f)) ▸ member

/-- The code's matching-family entry is the actual separated local component. -/
def codeComponent (φ : LocalArrow J p χ ((Separated.ofOriginal J p χ).obj a)
    ((Separated.ofOriginal J p χ).obj b))
    (d : D) (I : (codeCover J p χ K G φ d).Arrow) :
    (G.op ⋙ separatedHom J p χ a b φ.base).obj (op I.Y) :=
  separatedSection J p χ φ ⟨(G.obj I.Y).left, (G.obj I.Y).hom,
    codeCover_member J p χ K G φ d I⟩

/-- The actual entries form a compatible family on that original pulled-back cover. -/
theorem codeComponent_compatible
    (φ : LocalArrow J p χ ((Separated.ofOriginal J p χ).obj a)
      ((Separated.ofOriginal J p χ).obj b)) (d : D)
    (I : (codeCover J p χ K G φ d).Relation) :
    (G.op ⋙ separatedHom J p χ a b φ.base).map I.r.g₁.op
        (codeComponent J p χ K G φ d I.fst) =
      (G.op ⋙ separatedHom J p χ a b φ.base).map I.r.g₂.op
        (codeComponent J p χ K G φ d I.snd) := sorry

/-- The actual small matching-family multiequalizer element. -/
def codeMatchingFamily
    (φ : LocalArrow J p χ ((Separated.ofOriginal J p χ).obj a)
      ((Separated.ofOriginal J p χ).obj b)) (d : D) :
    multiequalizer ((codeCover J p χ K G φ d).index
      (G.op ⋙ separatedHom J p χ a b φ.base)) :=
  (Multiequalizer.lift _ (PUnit : Type vX)
    (fun I ↦ ↾fun _ ↦ codeComponent J p χ K G φ d I)
    (by intro I; ext; exact codeComponent_compatible J p χ K G φ d I)) PUnit.unit

/-- A representative gives its literal plus-construction class on the small local site. -/
def rawCode (φ : LocalArrow J p χ ((Separated.ofOriginal J p χ).obj a)
    ((Separated.ofOriginal J p χ).obj b)) (d : D) :
    (K.plusObj (G.op ⋙ separatedHom J p χ a b φ.base)).obj (op d) :=
  colimit.ι (K.diagram (G.op ⋙ separatedHom J p χ a b φ.base) d)
    (op (codeCover J p χ K G φ d)) (codeMatchingFamily J p χ K G φ d)

/-- Both the original base map and the actual small plus class are recorded. -/
def LocalArrowCode (d : D) : Type (max v vX) :=
  Σ g : p.obj a ⟶ p.obj b, (K.plusObj (G.op ⋙ separatedHom J p χ a b g)).obj (op d)

/-- Encode a local-arrow class using its native representative and actual family code. -/
def encodeLocalArrow (d : D)
    (τ : (Localized.category J p χ).Hom
      ((Localized.fromOriginal J p χ).obj a) ((Localized.fromOriginal J p χ).obj b)) :
    LocalArrowCode J p χ K G (b := b) d :=
  let φ : LocalArrow J p χ ((Separated.ofOriginal J p χ).obj a)
      ((Separated.ofOriginal J p χ).obj b) := Quotient.out τ
  ⟨φ.base, rawCode J p χ K G φ d⟩

/-- At a chart whose base arrow is invertible, equality of the small plus
codes is the original local-arrow quotient equality. -/
theorem encodeLocalArrow_injective
    (hG : CoverPreserving K (J.over (p.obj a)) G) (d : D) [IsIso (G.obj d).hom] :
    Function.Injective (encodeLocalArrow J p χ K G (b := b) d) := sorry

include K G in
/-- The specified small local-site code witnesses the original-universe Hom bound. -/
theorem localizedHomSmall
    (hG : CoverPreserving K (J.over (p.obj a)) G) (d : D) [IsIso (G.obj d).hom] :
    Small.{max v vX} ((Localized.category J p χ).Hom
      ((Localized.fromOriginal J p χ).obj a) ((Localized.fromOriginal J p χ).obj b)) :=
  small_of_injective (encodeLocalArrow_injective J p χ K G (b := b) hG d)

end CategoryTheory.Functor.StackificationConstruction
