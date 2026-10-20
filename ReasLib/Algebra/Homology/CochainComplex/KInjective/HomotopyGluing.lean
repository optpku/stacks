module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Tactic.CrossRefAttribute

/-! # Gluing strictly compatible homotopies over a degreewise colimit

Let `c` be a cocone over a diagram `F : J ⥤ HomologicalComplex V s` which is a colimit in each
degree, and let `f g : c.pt ⟶ D`. Suppose that for every `j` we are given a homotopy between
the restrictions `c.ι.app j ≫ f` and `c.ι.app j ≫ g`, and that these homotopies are strictly
compatible along the transition maps of `F`. Then their components descend degreewise along
the colimit cocones, and the descended components form an actual homotopy between `f` and `g`
which restricts to the given homotopy on every stage.

This is the limit-ordinal step in the proof of Stacks 079L: the stagewise nullhomotopies
produced by `CochainComplex.HomotopyExtension.extend` are strictly compatible (by
`CochainComplex.HomotopyExtension.f_extend_hom`), so at a limit stage `K_α = colim K_β` they
glue to an actual nullhomotopy without any Mittag-Leffler choice.

All components are colimit descents of the given components; no `Nonempty (Homotopy _ _)` is
consumed, and every statement here is proved.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w w' v u

namespace Homotopy

variable {V : Type u} [Category.{v} V] [Preadditive V]
variable {ι : Type*} {s : ComplexShape ι}
variable {J : Type w} [Category.{w'} J] {F : J ⥤ HomologicalComplex V s}
variable {c : Cocone F} {D : HomologicalComplex V s} {f g : c.pt ⟶ D}

/-- The cocone in degree `p` with vertex `D.X q` whose legs are the components
`(h j).hom p q` of strictly compatible stagewise homotopies. -/
@[simps]
def glueCocone (h : ∀ j : J, Homotopy (c.ι.app j ≫ f) (c.ι.app j ≫ g))
    (compat : ∀ ⦃j j' : J⦄ (φ : j ⟶ j') (p q : ι),
      (F.map φ).f p ≫ (h j').hom p q = (h j).hom p q) (p q : ι) :
    Cocone (F ⋙ HomologicalComplex.eval V s p) where
  pt := D.X q
  ι :=
    { app := fun j ↦ (h j).hom p q
      naturality := fun _ _ φ ↦ (compat φ p q).trans (Category.comp_id _).symm }

/-- The homotopy between `f` and `g` obtained by gluing strictly compatible homotopies on the
stages of a degreewise colimit cocone; its components are the colimit descents of the given
components. -/
@[stacks 079L "limit step: gluing compatible stagewise homotopies along a colimit"]
def glue (hc : ∀ n : ι, IsColimit ((HomologicalComplex.eval V s n).mapCocone c))
    (h : ∀ j : J, Homotopy (c.ι.app j ≫ f) (c.ι.app j ≫ g))
    (compat : ∀ ⦃j j' : J⦄ (φ : j ⟶ j') (p q : ι),
      (F.map φ).f p ≫ (h j').hom p q = (h j).hom p q) :
    Homotopy f g where
  hom p q := (hc p).desc (glueCocone h compat p q)
  zero p q hpq := (hc p).hom_ext fun j ↦ by
    rw [(hc p).fac]
    exact ((h j).zero p q hpq).trans Limits.comp_zero.symm
  comm i := (hc i).hom_ext fun j ↦ by
    have hfac : ∀ p q, (c.ι.app j).f p ≫ (hc p).desc (glueCocone h compat p q) =
        (h j).hom p q := fun p q ↦ (hc p).fac (glueCocone h compat p q) j
    have hj : (c.ι.app j).f i ≫ f.f i =
        dNext i (h j).hom + prevD i (h j).hom + (c.ι.app j).f i ≫ g.f i := by
      simpa only [HomologicalComplex.comp_f] using (h j).comm i
    have key : (c.ι.app j).f i ≫ f.f i = (c.ι.app j).f i ≫
        (dNext i (fun p q ↦ (hc p).desc (glueCocone h compat p q)) +
          prevD i (fun p q ↦ (hc p).desc (glueCocone h compat p q)) + g.f i) := by
      rw [hj]
      simp only [dNext, prevD, AddMonoidHom.mk'_apply]
      erw [Preadditive.comp_add, Preadditive.comp_add, HomologicalComplex.Hom.comm_assoc, hfac,
        reassoc_of% (hfac i (s.prev i))]
      rfl
    exact key

/-- The glued homotopy restricts to the given homotopy on every stage. -/
@[reassoc (attr := simp)]
lemma ι_glue_hom (hc : ∀ n : ι, IsColimit ((HomologicalComplex.eval V s n).mapCocone c))
    (h : ∀ j : J, Homotopy (c.ι.app j ≫ f) (c.ι.app j ≫ g))
    (compat : ∀ ⦃j j' : J⦄ (φ : j ⟶ j') (p q : ι),
      (F.map φ).f p ≫ (h j').hom p q = (h j).hom p q) (j : J) (p q : ι) :
    (c.ι.app j).f p ≫ (glue hc h compat).hom p q = (h j).hom p q :=
  (hc p).fac (glueCocone h compat p q) j

/-- Strictly compatible nullhomotopies of the restrictions `c.ι.app j ≫ f` glue to an actual
nullhomotopy of `f`; its components are the colimit descents of the given components. -/
def glueNullHomotopy (hc : ∀ n : ι, IsColimit ((HomologicalComplex.eval V s n).mapCocone c))
    (h : ∀ j : J, Homotopy (c.ι.app j ≫ f) 0)
    (compat : ∀ ⦃j j' : J⦄ (φ : j ⟶ j') (p q : ι),
      (F.map φ).f p ≫ (h j').hom p q = (h j).hom p q) :
    Homotopy f 0 :=
  glue (g := 0) hc (fun j ↦ (h j).trans (Homotopy.ofEq Limits.comp_zero.symm))
    (fun j j' φ p q ↦ by simpa using compat φ p q)

/-- The glued nullhomotopy restricts to the given nullhomotopy on every stage. -/
@[reassoc (attr := simp)]
lemma ι_glueNullHomotopy_hom
    (hc : ∀ n : ι, IsColimit ((HomologicalComplex.eval V s n).mapCocone c))
    (h : ∀ j : J, Homotopy (c.ι.app j ≫ f) 0)
    (compat : ∀ ⦃j j' : J⦄ (φ : j ⟶ j') (p q : ι),
      (F.map φ).f p ≫ (h j').hom p q = (h j).hom p q) (j : J) (p q : ι) :
    (c.ι.app j).f p ≫ (glueNullHomotopy hc h compat).hom p q = (h j).hom p q := by
  simp [glueNullHomotopy]

end Homotopy
