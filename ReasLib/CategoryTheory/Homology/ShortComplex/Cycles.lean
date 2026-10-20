module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cycle-to-Homology Maps for Short Complexes

This leaf module owns the canonical map from any cycle representative to the homology of a short
complex, its kernel specialization, and the induced subobject pullback. It is independent of any
particular presentation of a differential object.
@stack 0F7Y
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

namespace ShortComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The canonical map from a morphism into the cycles of a short complex to its homology. -/
@[stacks 0AMI "short-complex map to homology"]
noncomputable def liftToHomology (S : ShortComplex C) [S.HasHomology]
    {A : C} (f : A ⟶ S.X₂) (hf : f ≫ S.g = 0) :
    A ⟶ S.homology :=
  S.liftCycles f hf ≫ S.homologyπ

/-- The homology class of a cycle representative that is a boundary is zero. -/
@[reassoc, stacks 0AMI "boundary class vanishes"]
theorem liftToHomology_eq_zero_of_boundary (S : ShortComplex C) [S.HasHomology]
    {A : C} (f : A ⟶ S.X₂) (hf : f ≫ S.g = 0)
    {x : A ⟶ S.X₁} (hfx : f = x ≫ S.f) :
    S.liftToHomology f hf = 0 := sorry

namespace Cycles

/-- The canonical map from the kernel of the second differential of a short complex to its
homology object. -/
@[stacks 0AMI "short-complex cycles to homology"]
noncomputable def toHomology (S : ShortComplex C) [HasKernel S.g] [S.HasHomology] :
    (kernelSubobject S.g : C) ⟶ S.homology :=
  S.liftToHomology (kernelSubobject S.g).arrow (kernelSubobject_arrow_comp S.g)

/-- Pull a subobject of the homology of a short complex back along the canonical
cycles-to-homology map. -/
@[stacks 0AMI "short-complex homology subobject pullback"]
noncomputable def pullback (S : ShortComplex C) [HasKernel S.g] [S.HasHomology]
    [HasPullbacks C] (Z : Subobject S.homology) :
    Subobject (kernelSubobject S.g : C) :=
  (Subobject.pullback (toHomology S)).obj Z

/-- Regard the pullback of a homology subobject as a subobject of the middle object of the
short complex. -/
@[stacks 0AMI "short-complex homology subobject preimage"]
noncomputable def preimage (S : ShortComplex C) [HasKernel S.g] [S.HasHomology]
    [HasPullbacks C] (Z : Subobject S.homology) :
    Subobject S.X₂ :=
  (Subobject.map (kernelSubobject S.g).arrow).obj (pullback S Z)

/-- Pull a subobject back to the middle object of a short complex after identifying its ambient
object with the homology of that short complex. -/
@[stacks 0AMK, stacks 011Z "short-complex homology preimage along an isomorphism"]
noncomputable def preimageOfIso (S : ShortComplex C) [HasKernel S.g] [S.HasHomology]
    [HasPullbacks C] {A : C} (e : A ≅ S.homology) (Z : Subobject A) :
    Subobject S.X₂ :=
  preimage S ((Subobject.map e.hom).obj Z)

end Cycles

section Abelian

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A morphism of short complexes that is epic on homology and on the left term is epic on
cycles. This is the categorical boundary-correction argument: lift the homology class first,
then lift the boundary of the resulting error through the left component. -/
@[stacks 0F7Y "lifting cycles from homology and boundaries"]
theorem epi_cyclesMap_of_epi_homologyMap_of_epi_left
    {S₁ S₂ : ShortComplex A} (φ : S₁ ⟶ S₂)
    (hH : Epi (homologyMap φ)) (h₁ : Epi φ.τ₁) :
    Epi (cyclesMap φ) := sorry

/-- If the left component of a morphism of short complexes is epic, then its map on cycles is
epic exactly when its map on homology is epic. -/
@[stacks 0F7Y "epimorphy on cycles versus homology"]
theorem epi_cyclesMap_iff_epi_homologyMap_of_epi_left
    {S₁ S₂ : ShortComplex A} (φ : S₁ ⟶ S₂) (h₁ : Epi φ.τ₁) :
    Epi (cyclesMap φ) ↔ Epi (homologyMap φ) := sorry

/-- For an exact continuation of the homology map, epimorphy on cycles is equivalent to
vanishing of the next morphism, provided the left component is epic. -/
@[stacks 0F7Y "cycle epimorphy versus vanishing of the connecting morphism"]
theorem epi_cyclesMap_iff_eq_zero_of_exact
    {S₁ S₂ : ShortComplex A} (φ : S₁ ⟶ S₂) (h₁ : Epi φ.τ₁) {X : A}
    {δ : S₂.homology ⟶ X} {w : homologyMap φ ≫ δ = 0}
    (h : (ShortComplex.mk (homologyMap φ) δ w).Exact) :
    Epi (cyclesMap φ) ↔ δ = 0 := sorry

end Abelian

end ShortComplex

end CategoryTheory
