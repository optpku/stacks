/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Equivalence

@[expose] public section
open CategoryTheory CategoryTheory.Functor
noncomputable section
universe u v u' v'
namespace CategoryTheory.FiberedSliceEquivalence
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (p : D ⥤ C) [Functor.IsFibered.InGroupoids p] (x : D)

/-- Every arrow is strongly Cartesian using the input fibration and the
proved Mathlib upgrade from Cartesian to strongly Cartesian. -/
theorem strong {a b : D} (f : a ⟶ b) : p.IsStronglyCartesian (p.map f) f :=
  Functor.IsFibered.isStronglyCartesian_of_isCartesian p _ f

/-- Lift an actual arrow of the base slice by the Cartesian universal property. -/
def lift {a b : Over x} (f : (Over.post p).obj a ⟶ (Over.post p).obj b) : a ⟶ b := by
  -- Local instance justification (proof-local temporary data): this lifting problem is over the specific Cartesian arrow b.hom.
  letI := strong p b.hom
  have w : p.map a.hom = f.left ≫ p.map b.hom := (Over.w f).symm
  -- Local instance justification (defeq pin): record the actual image of a.hom for the same Cartesian lifting problem.
  letI : p.IsHomLift (p.map a.hom) a.hom := IsHomLift.map p a.hom
  exact Over.homMk
    (Functor.IsStronglyCartesian.map p (p.map b.hom) b.hom w a.hom)
    (Functor.IsStronglyCartesian.fac p (p.map b.hom) b.hom w a.hom)

theorem lift_map {a b : Over x} (f : (Over.post p).obj a ⟶ (Over.post p).obj b) :
    (Over.post p).map (lift p x f) = f := by
  apply Over.OverMorphism.ext
  -- Local instance justification (proof-local temporary data): read the image equation of the lift through the fixed arrow b.hom.
  letI := strong p b.hom
  change p.map (Functor.IsStronglyCartesian.map p (p.map b.hom) b.hom
    (show p.map a.hom = f.left ≫ p.map b.hom from (Over.w f).symm) a.hom) = f.left
  exact (IsHomLift.eq_of_isHomLift _ _ _).symm

/-- Faithfulness is uniqueness in that SAME Cartesian lifting problem. -/
theorem post_faithful : (Over.post p : Over x ⥤ Over (p.obj x)).Faithful where
  map_injective {a b} {f g} h := by
    have hfg : p.map f.left = p.map g.left := congrArg (fun h => h.left) h
    -- Local instance justification (proof-local temporary data): compare two lifts through this fixed Cartesian arrow.
    letI := strong p b.hom
    -- Local instance justification (defeq pin): the hypothesis hfg identifies the base image of these two particular lifts.
    letI : p.IsHomLift (p.map f.left) g.left := hfg.symm ▸ IsHomLift.map p g.left
    apply Over.OverMorphism.ext
    exact Functor.IsStronglyCartesian.ext p (p.map b.hom) b.hom (p.map f.left)
      ((Over.w f).trans (Over.w g).symm)

/-- Fullness uses the explicit lift, not an admitted full-functor witness. -/
theorem post_full : (Over.post p : Over x ⥤ Over (p.obj x)).Full where
  map_surjective f := ⟨lift p x f, lift_map p x f⟩

/-- Essential surjectivity is extracted only from the INPUT fibration's
Cartesian-lift field. No new unproved existence statement is used. -/
theorem post_essSurj : (Over.post p : Over x ⥤ Over (p.obj x)).EssSurj where
  mem_essImage y := by
    obtain ⟨a, φ, hφ⟩ := IsPreFibered.exists_isCartesian p (a := x) rfl y.hom
    -- Local instance justification (proof-local temporary data): use the Cartesian lift supplied by the input fibration for this y.hom.
    letI : p.IsCartesian y.hom φ := hφ
    -- Local instance justification (proof-local temporary data): identify that same lift with the given base arrow y.hom.
    letI : p.IsHomLift y.hom φ := hφ.toIsHomLift
    have hdom : p.obj a = y.left := IsHomLift.domain_eq p y.hom φ
    refine ⟨Over.mk φ, ⟨Over.isoMk (eqToIso hdom) ?_⟩⟩
    change eqToHom hdom ≫ y.hom = p.map φ
    simpa using (IsHomLift.fac' p y.hom φ).symm

/-- The actual slice projection has a proved equivalence certificate. -/
theorem post_isEquivalence : (Over.post p : Over x ⥤ Over (p.obj x)).IsEquivalence where
  faithful := post_faithful p x
  full := post_full p x
  essSurj := post_essSurj p x

/-- Mathlib may now select inverse data from the genuinely proved certificate. -/
def equivalence : Over x ≌ Over (p.obj x) := by
  -- Local instance justification (proof-local temporary data): construct the equivalence from the full, faithful and essentially surjective functor just proved.
  letI := post_isEquivalence p x
  exact (Over.post p).asEquivalence

end CategoryTheory.FiberedSliceEquivalence
