/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.Cech.Conerve.Coprojection
public import ReasLib.AlgebraicTopology.Cech.Conerve.Opposite.Iso
public import Mathlib.AlgebraicTopology.CechNerve
public import ReasLib.AlgebraicTopology.Cech.Nerve.SplitEpi.Section
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Retractions of split Čech conerves

This module owns the functorial Čech-conerve retract associated to a bundled split
monomorphism.  An explicit retraction and its identity enter this API through `SplitMono.mk`.
-/

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X Y : C} {f : X ⟶ Y}
variable [(Arrow.mk f).HasCechConerve]

namespace SplitMono

namespace cechConerve

namespace retractionEndomorphism

/-- The chosen retraction square commutes with the split monomorphism. -/
@[stacks 019Z "split Čech-conerve retraction square"]
theorem arrowHom.w (r : SplitMono f) :
    𝟙 X ≫ f = f ≫ (r.retraction ≫ f) := sorry

/-- The arrow endomorphism induced by the chosen retraction of a split monomorphism. -/
@[stacks 019Z "split Čech-conerve retraction arrow endomorphism"]
def arrowHom (r : SplitMono f) :
    Arrow.mk f ⟶ Arrow.mk f :=
  Arrow.homMk (𝟙 X) (r.retraction ≫ f) (arrowHom.w r)

/-- The Čech-conerve endomorphism induced by a chosen retraction of a split monomorphism. -/
@[stacks 019Z "split Čech-conerve retraction endomorphism"]
def map (r : SplitMono f) :
    (Arrow.mk f).cechConerve ⟶ (Arrow.mk f).cechConerve :=
  Arrow.mapCechConerve (arrowHom r)

namespace map

/-- The retraction-induced endomorphism acts on every Cech-conerve vertex through the
idempotent `r.retraction ≫ f`. -/
@[reassoc (attr := simp), stacks 019Z "split Cech-conerve endomorphism on vertices"]
theorem app_ι (r : SplitMono f) (n : SimplexCategory) (i : Fin (n.len + 1)) :
    Arrow.cechConerve.ι (Arrow.mk f) n i ≫
        (retractionEndomorphism.map r).app n =
      (r.retraction ≫ f) ≫ Arrow.cechConerve.ι (Arrow.mk f) n i := sorry

end map

end retractionEndomorphism

namespace retraction

/-- The degreewise retraction from the Čech conerve to the source of a split monomorphism. -/
@[stacks 019Z "degreewise split Čech-conerve retraction"]
def app (r : SplitMono f) (n : SimplexCategory) :
    ((Arrow.mk f).cechConerve.obj n) ⟶ X :=
  Arrow.cechConerve.desc (Arrow.mk f) n (𝟙 X)
    (fun _ : Fin (n.len + 1) ↦ r.retraction) (fun _ ↦ r.id)

/-- The degreewise retraction sends each Cech-conerve vertex coprojection to the chosen
retraction. -/
@[reassoc (attr := simp), stacks 019Z "split Cech-conerve retraction on vertices"]
theorem app_ι (r : SplitMono f) (n : SimplexCategory) (i : Fin (n.len + 1)) :
    Arrow.cechConerve.ι (Arrow.mk f) n i ≫ app r n = r.retraction := sorry

/-- The degreewise retraction sends the Cech-conerve head coprojection to the identity. -/
@[reassoc (attr := simp), stacks 019Z "split Cech-conerve retraction on the head"]
theorem app_head (r : SplitMono f) (n : SimplexCategory) :
    Arrow.cechConerve.head (Arrow.mk f) n ≫ app r n = 𝟙 X := sorry

/-- The degreewise retractions of a split monomorphism commute with simplex operators. -/
@[stacks 019Z "split Čech-conerve retraction naturality"]
theorem naturality (r : SplitMono f)
    {n m : SimplexCategory} (α : n ⟶ m) :
    ((Arrow.mk f).cechConerve).map α ≫ app r m =
      app r n ≫ ((CosimplicialObject.const C).obj X).map α := sorry

/-- The Čech conerve of a split monomorphism retracts to the constant cosimplicial object on its
source. -/
@[stacks 019Z "split Čech-conerve retraction"]
def hom (r : SplitMono f) :
    (Arrow.mk f).cechConerve ⟶ (CosimplicialObject.const C).obj X :=
  { app := app r
    naturality := fun _ _ α ↦ naturality r α }

namespace hom

/-- The components of the Cech-conerve retraction natural transformation are the degreewise
descent maps. -/
@[simp, stacks 019Z "split Cech-conerve retraction component"]
theorem app (r : SplitMono f) (n : SimplexCategory) :
    (retraction.hom r).app n = retraction.app r n := sorry

end hom

/-- The Čech-conerve retraction is compatible with its coaugmentation and the constant
coaugmentation. -/
@[stacks 019Z "split Čech-conerve retraction coaugmentation compatibility"]
theorem augmented.w (r : SplitMono f) :
    (CosimplicialObject.const C).map (𝟙 X) ≫
        ((CosimplicialObject.Augmented.const).obj X).hom =
      (Arrow.mk f).augmentedCechConerve.hom ≫ hom r := sorry

/-- The augmented Čech-conerve retraction associated to a chosen split monomorphism. -/
@[stacks 019Z "augmented split Čech-conerve retraction"]
def augmented (r : SplitMono f) :
    (Arrow.mk f).augmentedCechConerve ⟶ (CosimplicialObject.Augmented.const).obj X where
  left := 𝟙 X
  right := hom r
  w := augmented.w r

end retraction

namespace coaugmentation

/-- The Čech-conerve coaugmentation is a right inverse to the retraction of a split
monomorphism. -/
@[reassoc (attr := simp), stacks 019Z "split Čech-conerve coaugmentation retraction"]
theorem comp_retraction (r : SplitMono f) :
    (Arrow.mk f).augmentedCechConerve.hom ≫ retraction.hom r =
      𝟙 ((CosimplicialObject.const C).obj X) := sorry

end coaugmentation

namespace retraction

/-- Composing the Čech-conerve retraction with its coaugmentation yields the retraction-induced
endomorphism of the chosen split monomorphism. -/
@[reassoc (attr := simp), stacks 019Z "split Čech-conerve retraction identity"]
theorem comp_coaugmentation (r : SplitMono f) :
    hom r ≫ (Arrow.mk f).augmentedCechConerve.hom =
      retractionEndomorphism.map r := sorry

/-- The conerve retraction is the opposite of the canonical section on the opposite arrow,
transported across the natural Čech comparison. -/
@[stacks 019Z "split Cech-conerve retraction opposite-section bridge"]
theorem hom_eq_opposite (r : SplitMono f) :
    hom r =
      (Arrow.cechConerve.opposite.iso f).hom ≫
        NatTrans.unop
          (SplitEpi.cechNerve.sectionMap.hom (f := f.op) r.op) := sorry

end retraction

end cechConerve

end SplitMono

end CategoryTheory
