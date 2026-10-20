module

public import Mathlib.Algebra.Homology.HomotopyCofiber
public import ReasLib.CategoryTheory.Homology.DegreewiseSplit.Chain
public import ReasLib.CategoryTheory.Homology.DegreewiseSplit.ShortExact
import Mathlib.Tactic.CrossRefAttribute

/-!
# The degreewise split short complex of a homotopy cofiber

For a chain map `φ : K ⟶ L`, its homotopy cofiber fits into the canonical degreewise split
short complex

`L ⟶ HomologicalComplex.homotopyCofiber φ ⟶ K⟦-1⟧`.

The chosen splitting identifies the associated chain connecting map with `φ⟦-1⟧'`.  This is the
generic owner underlying mapping-cone and cylinder long exact sequences.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section

universe v u

namespace ChainComplex.homotopyCofiber

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {K L : ChainComplex C ℤ}

/-- The canonical inclusion `L ⟶ HomologicalComplex.homotopyCofiber φ`. -/
@[stacks 01A3 "homotopy-cofiber short-complex inclusion"]
def inclusion (φ : K ⟶ L) : L ⟶ HomologicalComplex.homotopyCofiber φ :=
  HomologicalComplex.homotopyCofiber.inr φ

/-- The degree-`n` component of the canonical projection from the homotopy cofiber to
`K⟦-1⟧`. -/
@[stacks 01A3 "homotopy-cofiber short-complex projection component"]
def projectionApp (φ : K ⟶ L) (n : ℤ) :
    (HomologicalComplex.homotopyCofiber φ).X n ⟶ (K⟦(-1 : ℤ)⟧).X n :=
  HomologicalComplex.homotopyCofiber.fstX φ n (n - 1)
      (ComplexShape.down_mk n (n - 1) (sub_add_cancel n 1)) ≫
    (Shift.MinusOne.xIso K n).inv

/-- The homotopy-cofiber projection components commute with the chain differentials. -/
@[stacks 01A3 "homotopy-cofiber short-complex projection naturality"]
theorem projectionApp_comm (φ : K ⟶ L) (i j : ℤ)
    (hij : (ComplexShape.down ℤ).Rel i j) :
    projectionApp φ i ≫ (K⟦(-1 : ℤ)⟧).d i j =
      (HomologicalComplex.homotopyCofiber φ).d i j ≫ projectionApp φ j := sorry

/-- The canonical projection `HomologicalComplex.homotopyCofiber φ ⟶ K⟦-1⟧`. -/
@[stacks 01A3 "homotopy-cofiber short-complex projection"]
def projection (φ : K ⟶ L) :
    HomologicalComplex.homotopyCofiber φ ⟶ K⟦(-1 : ℤ)⟧ where
  f := projectionApp φ
  comm' := projectionApp_comm φ

/-- The degree components of the bundled homotopy-cofiber projection are `projectionApp`. -/
@[simp, stacks 01A3 "homotopy-cofiber short-complex projection component formula"]
theorem projection_f (φ : K ⟶ L) (n : ℤ) :
    (projection φ).f n = projectionApp φ n := sorry

/-- The composite of the homotopy-cofiber inclusion and projection is zero. -/
@[stacks 01A3 "homotopy-cofiber short-complex zero composite"]
theorem inclusion_comp_projection (φ : K ⟶ L) :
    inclusion φ ≫ projection φ = 0 := sorry

/-- The canonical short complex `L ⟶ HomologicalComplex.homotopyCofiber φ ⟶ K⟦-1⟧`. -/
@[stacks 01A3 "homotopy-cofiber short complex"]
def shortComplex (φ : K ⟶ L) : ShortComplex (ChainComplex C ℤ) :=
  ShortComplex.mk (inclusion φ) (projection φ) (inclusion_comp_projection φ)

/-- The first map of the homotopy-cofiber short complex is its canonical inclusion. -/
@[simp, stacks 01A3 "homotopy-cofiber short-complex first map formula"]
theorem shortComplex_f (φ : K ⟶ L) :
    (shortComplex φ).f = inclusion φ := sorry

/-- The second map of the homotopy-cofiber short complex is its canonical projection. -/
@[simp, stacks 01A3 "homotopy-cofiber short-complex second map formula"]
theorem shortComplex_g (φ : K ⟶ L) :
    (shortComplex φ).g = projection φ := sorry

/-- The retraction of the homotopy-cofiber inclusion in degree `n`. -/
@[stacks 01A3 "homotopy-cofiber short-complex retraction component"]
def retractionApp (φ : K ⟶ L) (n : ℤ) :
    (HomologicalComplex.homotopyCofiber φ).X n ⟶ L.X n :=
  HomologicalComplex.homotopyCofiber.sndX φ n

/-- The section of the homotopy-cofiber projection in degree `n`. -/
@[stacks 01A3 "homotopy-cofiber short-complex section component"]
def sectionApp (φ : K ⟶ L) (n : ℤ) :
    (K⟦(-1 : ℤ)⟧).X n ⟶ (HomologicalComplex.homotopyCofiber φ).X n :=
  (Shift.MinusOne.xIso K n).hom ≫
    HomologicalComplex.homotopyCofiber.inlX φ (n - 1) n
      (ComplexShape.down_mk n (n - 1) (sub_add_cancel n 1))

/-- The degreewise homotopy-cofiber inclusion followed by its retraction is the identity. -/
@[stacks 01A3 "homotopy-cofiber inclusion retraction formula"]
theorem inclusion_comp_retraction (φ : K ⟶ L) (n : ℤ) :
    (inclusion φ).f n ≫ retractionApp φ n = 𝟙 _ := sorry

/-- The degreewise section followed by the homotopy-cofiber projection is the identity. -/
@[stacks 01A3 "homotopy-cofiber section projection formula"]
theorem section_comp_projection (φ : K ⟶ L) (n : ℤ) :
    sectionApp φ n ≫ (projection φ).f n = 𝟙 _ := sorry

/-- The homotopy-cofiber retraction and section decompose the degreewise identity. -/
@[stacks 01A3 "homotopy-cofiber splitting identity"]
theorem splitting_id (φ : K ⟶ L) (n : ℤ) :
    (retractionApp φ n ≫ (inclusion φ).f n) +
        ((projection φ).f n ≫ sectionApp φ n) =
      𝟙 _ := sorry

/-- The canonical degreewise splitting of the homotopy-cofiber short complex. -/
@[stacks 01A3 "degreewise homotopy-cofiber splitting"]
def splitting (φ : K ⟶ L) : ShortComplex.DegreewiseSplitting (shortComplex φ) :=
  fun n ↦
    { r := retractionApp φ n
      s := sectionApp φ n
      f_r := inclusion_comp_retraction φ n
      s_g := section_comp_projection φ n
      id := splitting_id φ n }

/-- The retraction in the canonical homotopy-cofiber splitting is `retractionApp`. -/
@[simp, stacks 01A3 "homotopy-cofiber splitting retraction formula"]
theorem splitting_r (φ : K ⟶ L) (n : ℤ) :
    (splitting φ n).r = retractionApp φ n := sorry

/-- The section in the canonical homotopy-cofiber splitting is `sectionApp`. -/
@[simp, stacks 01A3 "homotopy-cofiber splitting section formula"]
theorem splitting_s (φ : K ⟶ L) (n : ℤ) :
    (splitting φ n).s = sectionApp φ n := sorry

/-- The connecting map of the homotopy-cofiber short complex is the shifted original map. -/
@[stacks 01A3 "boundary map of the homotopy-cofiber short complex"]
theorem boundary_eq (φ : K ⟶ L) :
    homOfDegreewiseSplit (shortComplex φ) (splitting φ) =
      φ⟦(-1 : ℤ)⟧' := sorry

end ChainComplex.homotopyCofiber

namespace ChainComplex.homotopyCofiber.shortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : ChainComplex C ℤ}

/-- The canonical homotopy-cofiber short complex is short exact. -/
@[stacks 01A3 "homotopy-cofiber short exact sequence"]
theorem shortExact (φ : K ⟶ L) :
    (ChainComplex.homotopyCofiber.shortComplex φ).ShortExact := sorry

end ChainComplex.homotopyCofiber.shortComplex
