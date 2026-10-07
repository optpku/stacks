module

public import ReasLib.AlgebraicTopology.Cech.Nerve.SplitEpi.Section
public import ReasLib.AlgebraicTopology.Cech.Existence
public import ReasLib.AlgebraicTopology.SimplicialObject.HomotopyEquiv

@[expose] public section

/-!
@stack 019P

# Homotopy contraction of a split Čech nerve

The extra degeneracy on the augmented Čech nerve of a split epimorphism contracts the
section-induced endomorphism to the identity.  The API is attached to the bundled
`CategoryTheory.SplitEpi`; explicit section data enters through `SplitEpi.mk`.
-/

open CategoryTheory
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X Y : C} {f : X ⟶ Y}
variable [(Arrow.mk f).HasCechNerve]

namespace SplitEpi

namespace cechNerve

namespace sectionEndomorphism

/-- The source of the standard extra-degeneracy homotopy is the Čech-nerve endomorphism induced
by the chosen section. -/
@[stacks 019P "split Čech-nerve extra-degeneracy source"]
theorem map.eq_extraDegeneracySource (S : SplitEpi f) :
    sectionEndomorphism.map (f := f) S =
      (Arrow.mk f).augmentedCechNerve.hom ≫
        (Arrow.AugmentedCechNerve.extraDegeneracy (Arrow.mk f) S).section_ := sorry

namespace homotopy

/-- The component family of the split Čech-nerve contraction, inherited from the canonical
extra degeneracy. -/
@[stacks 019P "split Čech-nerve contraction components"]
def component (S : SplitEpi f) {n : ℕ} (i : Fin (n + 1)) :
    (Arrow.mk f).cechNerve _⦋n⦌ ⟶ (Arrow.mk f).cechNerve _⦋n + 1⦌ :=
  (Arrow.AugmentedCechNerve.extraDegeneracy (Arrow.mk f) S).homotopy.h i

namespace component

namespace face

/-- The zero face of the first contraction component is the identity endpoint. -/
@[stacks 019P "split Cech contraction zero-face component"]
theorem zero_comp (S : SplitEpi f) (n : ℕ) :
    component S 0 ≫ (Arrow.mk f).cechNerve.δ 0 =
      (𝟙 ((Arrow.mk f).cechNerve) :
        (Arrow.mk f).cechNerve ⟶ (Arrow.mk f).cechNerve).app
          (Opposite.op ⦋n⦌) := sorry

/-- The last face of the last contraction component is the section-endomorphism endpoint. -/
@[stacks 019P "split Cech contraction last-face component"]
theorem last_comp (S : SplitEpi f) (n : ℕ) :
    component S (Fin.last n) ≫ (Arrow.mk f).cechNerve.δ (Fin.last (n + 1)) =
      (sectionEndomorphism.map (f := f) S).app (Opposite.op ⦋n⦌) := sorry

/-- The contraction components satisfy the first interior coface identity. -/
@[stacks 019P "split Cech contraction first interior coface"]
theorem succ_comp_castSucc_of_lt (S : SplitEpi f)
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    component S j.succ ≫ (Arrow.mk f).cechNerve.δ i.castSucc =
      (Arrow.mk f).cechNerve.δ i ≫ component S j := sorry

/-- The contraction components satisfy the adjacent coface identity. -/
@[stacks 019P "split Cech contraction adjacent coface"]
theorem succ_comp_castSucc_succ (S : SplitEpi f)
    {n : ℕ} (j : Fin (n + 1)) :
    component S j.succ ≫ (Arrow.mk f).cechNerve.δ j.castSucc.succ =
      component S j.castSucc ≫ (Arrow.mk f).cechNerve.δ j.castSucc.succ := sorry

/-- The contraction components satisfy the second interior coface identity. -/
@[stacks 019P "split Cech contraction second interior coface"]
theorem castSucc_comp_succ_of_lt (S : SplitEpi f)
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) :
    component S j.castSucc ≫ (Arrow.mk f).cechNerve.δ i.succ =
      (Arrow.mk f).cechNerve.δ i ≫ component S j := sorry

end face

namespace degeneracy

/-- The contraction components satisfy the first codegeneracy identity. -/
@[stacks 019P "split Cech contraction first codegeneracy"]
theorem comp_castSucc_of_le (S : SplitEpi f)
    {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    component S j ≫ (Arrow.mk f).cechNerve.σ i.castSucc =
      (Arrow.mk f).cechNerve.σ i ≫ component S j.succ := sorry

/-- The contraction components satisfy the second codegeneracy identity. -/
@[stacks 019P "split Cech contraction second codegeneracy"]
theorem comp_succ_of_lt (S : SplitEpi f)
    {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) :
    component S j ≫ (Arrow.mk f).cechNerve.σ i.succ =
      (Arrow.mk f).cechNerve.σ i ≫ component S j.castSucc := sorry

end degeneracy

end component

end homotopy

/-- Lemma 14.26.9 (`019P`): the section-induced endomorphism of the Čech nerve of a split
epimorphism is connected to the identity by the canonical extra-degeneracy homotopy. Its
non-propositional family `h` is inherited directly from `ExtraDegeneracy.homotopy`. -/
@[stacks 019P "split Čech-nerve contraction"]
def homotopy (S : SplitEpi f) :
    SimplicialObject.Homotopy
      (sectionEndomorphism.map (f := f) S)
      (𝟙 (Arrow.mk f).cechNerve) :=
  SimplicialObject.Homotopy.cast
    (map.eq_extraDegeneracySource (f := f) S).symm rfl
    (Arrow.AugmentedCechNerve.extraDegeneracy (Arrow.mk f) S).homotopy

/-- The homotopy components of the split Čech-nerve contraction are exactly those of the
canonical extra-degeneracy homotopy. -/
@[simp, stacks 019P "split Cech contraction homotopy components"]
theorem homotopy.hom (S : SplitEpi f)
    {n : ℕ} (i : Fin (n + 1)) :
    (homotopy (f := f) S).h i =
      (Arrow.AugmentedCechNerve.extraDegeneracy (Arrow.mk f) S).homotopy.h i := sorry

/-- The section-induced endomorphism of a split Čech nerve is homotopic to the identity. -/
@[stacks 019P "split Čech-nerve contraction relation"]
theorem homotopic_id (S : SplitEpi f) :
    SimplicialObject.Homotopic
      (sectionEndomorphism.map (f := f) S)
      (𝟙 (Arrow.mk f).cechNerve) := sorry

end sectionEndomorphism

namespace sectionMap.comp_augmentation

/-- Canonical relation API for the split section followed by the augmentation. -/
@[stacks 019P "split Cech section-augmentation homotopy relation"]
theorem homotopic_id (S : SplitEpi f) :
    SimplicialObject.Homotopic
      (sectionMap.hom (f := f) S ≫ (Arrow.mk f).augmentedCechNerve.hom)
      (𝟙 ((SimplicialObject.const C).obj Y)) := sorry

end sectionMap.comp_augmentation

namespace augmentation

/-- Canonical relation API for the augmentation followed by the split section. -/
@[stacks 019P "split Cech augmentation-section homotopy relation"]
theorem comp_section.homotopic_id (S : SplitEpi f) :
    SimplicialObject.Homotopic
      ((Arrow.mk f).augmentedCechNerve.hom ≫ sectionMap.hom (f := f) S)
      (𝟙 (Arrow.mk f).cechNerve) := sorry

/-- The Čech-nerve augmentation of a split epimorphism, together with its canonical section,
forms a simplicial homotopy equivalence. -/
@[stacks 019P "split Čech-nerve augmentation homotopy equivalence"]
def homotopyEquiv (S : SplitEpi f) :
    SimplicialObject.HomotopyEquiv
      (Arrow.mk f).cechNerve ((SimplicialObject.const C).obj Y) where
  hom := (Arrow.mk f).augmentedCechNerve.hom
  inv := sectionMap.hom (f := f) S
  hom_inv_id := comp_section.homotopic_id S
  inv_hom_id := sectionMap.comp_augmentation.homotopic_id S

/-- The forward map of the split Čech-nerve homotopy equivalence is its augmentation. -/
@[simp, stacks 019P "forward map of the split Čech-nerve homotopy equivalence"]
theorem homotopyEquiv.hom (S : SplitEpi f) :
    (homotopyEquiv S).hom = (Arrow.mk f).augmentedCechNerve.hom := sorry

/-- The inverse map of the split Čech-nerve homotopy equivalence is the canonical section. -/
@[simp, stacks 019P "inverse map of the split Čech-nerve homotopy equivalence"]
theorem homotopyEquiv.inv (S : SplitEpi f) :
    (homotopyEquiv S).inv = sectionMap.hom (f := f) S := sorry

/-- The augmentation of the Čech nerve of a split epimorphism is a simplicial homotopy
equivalence. -/
@[stacks 019P "split Čech-nerve augmentation equivalence property"]
theorem isHomotopyEquivalence (S : SplitEpi f) :
    SimplicialObject.IsHomotopyEquivalence
      (Arrow.mk f).augmentedCechNerve.hom := sorry

end augmentation

end cechNerve

end SplitEpi

end CategoryTheory
