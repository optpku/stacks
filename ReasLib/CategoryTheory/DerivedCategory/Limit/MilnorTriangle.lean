module

public import ReasLib.CategoryTheory.InverseSystem.Milnor.Derived
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived Limits and Milnor Triangles

For a sequential inverse system `Ksys : SequentialInverseSystem D` in a preadditive category `D`,
this module uses the canonical Milnor difference endomorphism `1 - shift` of `∏ Ksys.family` to
define the first derived limit `R¹ lim Ksys` as a cokernel and, in a triangulated category, the
notion of a derived limit (homotopy limit) via a Milnor distinguished triangle.

## Main definitions

* `SequentialInverseSystem.family` -- the family `n ↦ Ksys.obj (op n)` underlying `Ksys`.
* `DerivedLimit.R1` -- the cokernel of the Milnor difference endomorphism.
* `DerivedLimit.R1.map` -- the induced map on Milnor cokernels under a morphism of inverse systems.
* `HasMilnorTriangle` -- `K` is equipped with a distinguished Milnor triangle for `Ksys`.
* `IsDerivedLimit` -- `K` is a derived limit (homotopy limit) of `Ksys`.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Opposite

noncomputable section

universe v u

namespace CategoryTheory

namespace DerivedLimit

section

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasCokernels D]

/-- The first derived inverse limit, modeled by the cokernel of the Milnor difference map. -/
abbrev R1 (Ksys : SequentialInverseSystem D) [HasProduct Ksys.family] :=
  SequentialInverseSystem.Milnor.ProductCone.canonicalR1 Ksys

namespace R1

/-- The canonical quotient from the product to the first derived inverse limit. -/
abbrev π (Ksys : SequentialInverseSystem D) [HasProduct Ksys.family] :
    ∏ᶜ Ksys.family ⟶ R1 Ksys :=
  SequentialInverseSystem.Milnor.ProductCone.canonicalR1.π Ksys

/-- The map on first derived inverse limits induced by a morphism of sequential inverse systems. -/
abbrev map {Ksys Lsys : SequentialInverseSystem D}
    [HasProduct Ksys.family] [HasProduct Lsys.family] (φ : Ksys ⟶ Lsys) :
    R1 Ksys ⟶ R1 Lsys :=
  SequentialInverseSystem.Milnor.ProductCone.canonicalR1.map φ

/-- The quotient maps defining `R¹ lim` are natural under a morphism of sequential inverse
systems. -/
@[reassoc]
theorem π_map {Ksys Lsys : SequentialInverseSystem D}
    [HasProduct Ksys.family] [HasProduct Lsys.family] (φ : Ksys ⟶ Lsys) :
    π Ksys ≫ map φ = SequentialInverseSystem.productMap φ ≫ π Lsys := sorry

section

variable [HasCountableProducts D]

/-- The functor sending a sequential inverse system to its Milnor cokernel. -/
abbrev functor : SequentialInverseSystem D ⥤ D :=
  SequentialInverseSystem.Milnor.ProductCone.canonicalR1.functor

/-- The object of the first-derived-limit functor is the Milnor cokernel model. -/
@[simp]
theorem functor_obj (Ksys : SequentialInverseSystem D) :
    functor.obj Ksys = R1 Ksys := sorry

/-- The morphism of the first-derived-limit functor is the map induced on Milnor cokernels. -/
@[simp]
theorem functor_map {Ksys Lsys : SequentialInverseSystem D} (φ : Ksys ⟶ Lsys) :
    functor.map φ = map φ := sorry

end

end R1

end

end DerivedLimit

/-!
## First derived inverse limits

The first derived inverse limit of a sequential system is the cokernel of its Milnor
difference endomorphism. Morphisms of systems induce morphisms of these cokernels.
-/

namespace SequentialInverseSystem

section

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasCokernels D]

/-- The first derived inverse limit as the cokernel of the Milnor difference endomorphism. -/
abbrev firstDerivedLimit (Ksys : SequentialInverseSystem D) [HasProduct Ksys.family] : D :=
  DerivedLimit.R1 Ksys

/-- The map on Milnor cokernels induced by a morphism of inverse systems. -/
abbrev firstDerivedLimitMap {Ksys Lsys : SequentialInverseSystem D}
    [HasProduct Ksys.family] [HasProduct Lsys.family] (φ : Ksys ⟶ Lsys) :
    Ksys.firstDerivedLimit ⟶ Lsys.firstDerivedLimit :=
  DerivedLimit.R1.map φ

end

end SequentialInverseSystem

section SourceNames

variable {D : Type u} [Category.{v} D] [Preadditive D]

/-- The family of stage objects of a sequential inverse system. -/
abbrev inverseSystemFamily (Ksys : SequentialInverseSystem D) : ℕ → D :=
  Ksys.family

/-- The Milnor difference endomorphism of the product of the stage objects. -/
abbrev derivedLimitDifferenceMap (Ksys : SequentialInverseSystem D)
    [HasProduct Ksys.family] :
    ∏ᶜ inverseSystemFamily Ksys ⟶ ∏ᶜ inverseSystemFamily Ksys :=
  Ksys.milnorDifferenceMap

/-- The projection of the Milnor difference is the current projection minus the next projection
followed by the transition map. -/
@[reassoc (attr := simp)]
theorem derivedLimitDifferenceMap_comp_π (Ksys : SequentialInverseSystem D)
    [HasProduct Ksys.family] (n : ℕ) :
    derivedLimitDifferenceMap Ksys ≫ Pi.π (inverseSystemFamily Ksys) n =
      Pi.π (inverseSystemFamily Ksys) n -
        Pi.π (inverseSystemFamily Ksys) (n + 1) ≫ Ksys.transitionMap (Nat.le_succ n) := sorry

/-- The Milnor difference endomorphism commutes with the product map induced by a morphism
of inverse systems. -/
@[reassoc]
theorem derivedLimitDifferenceMap_naturality
    {Ksys Lsys : SequentialInverseSystem D}
    [HasProduct Ksys.family] [HasProduct Lsys.family] (φ : Ksys ⟶ Lsys) :
    derivedLimitDifferenceMap Ksys ≫ SequentialInverseSystem.productMap φ =
      SequentialInverseSystem.productMap φ ≫ derivedLimitDifferenceMap Lsys := sorry

end SourceNames

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- A Milnor triangle for a sequential inverse system `Ksys` and an object `K`:
a distinguished triangle `K → ∏ Kₙ → ∏ Kₙ → K⟦1⟧` whose middle morphism is the
canonical difference map `1 - shift`. -/
@[stacks 08TC]
structure HasMilnorTriangle (Ksys : SequentialInverseSystem D)
    [HasProduct Ksys.family] (K : D) where
  /-- The inclusion `K → ∏ Kₙ`. -/
  ι : K ⟶ ∏ᶜ Ksys.family
  /-- The connecting morphism `∏ Kₙ → K⟦1⟧`. -/
  δ : ∏ᶜ Ksys.family ⟶ K⟦(1 : ℤ)⟧
  /-- The triangle is distinguished. -/
  mem_distTriang : Triangle.mk ι Ksys.milnorDifferenceMap δ ∈ distTriang D

namespace HasMilnorTriangle

/-- A Milnor triangle whose first map to the product is prescribed. -/
@[stacks 08TC]
def WithMap (Ksys : SequentialInverseSystem D) [HasProduct Ksys.family]
  {K : D} (ι : K ⟶ ∏ᶜ Ksys.family) : Prop :=
  ∃ δ : ∏ᶜ Ksys.family ⟶ K⟦(1 : ℤ)⟧,
    Triangle.mk ι Ksys.milnorDifferenceMap δ ∈ distTriang D

namespace WithMap

/-- A Milnor presentation with a prescribed first map determines a Milnor triangle. -/
noncomputable def toTriangle {Ksys : SequentialInverseSystem D} [HasProduct Ksys.family]
    {K : D} {ι : K ⟶ ∏ᶜ Ksys.family} (h : WithMap Ksys ι) :
    HasMilnorTriangle Ksys K where
  ι := ι
  δ := Classical.choose h
  mem_distTriang := Classical.choose_spec h

/-- The Milnor triangle selected from a prescribed-map presentation retains that first map. -/
@[simp, stacks 08TC]
theorem toTriangle_ι {Ksys : SequentialInverseSystem D} [HasProduct Ksys.family]
    {K : D} {ι : K ⟶ ∏ᶜ Ksys.family} (h : WithMap Ksys ι) :
    h.toTriangle.ι = ι := sorry

/-- The connecting morphism selected from a prescribed-map presentation completes a
distinguished Milnor triangle. -/
@[stacks 08TC]
theorem toTriangle_mem_distTriang
    {Ksys : SequentialInverseSystem D} [HasProduct Ksys.family]
    {K : D} {ι : K ⟶ ∏ᶜ Ksys.family} (h : WithMap Ksys ι) :
    Triangle.mk ι Ksys.milnorDifferenceMap h.toTriangle.δ ∈
      distTriang D := sorry

end WithMap

/-- A Milnor triangle supplies the corresponding presentation with its first map prescribed. -/
@[stacks 08TC]
theorem withMap {Ksys : SequentialInverseSystem D} [HasProduct Ksys.family]
    {K : D} (h : HasMilnorTriangle Ksys K) : WithMap Ksys h.ι := sorry

/-- The distinguished triangle underlying a Milnor triangle. -/
def triangle {Ksys : SequentialInverseSystem D} [HasProduct Ksys.family]
    {K : D} (h : HasMilnorTriangle Ksys K) : Triangle D :=
  Triangle.mk h.ι Ksys.milnorDifferenceMap h.δ

namespace ObjectIso

/-- The first morphism in the Milnor triangle transported along an isomorphism of its first
object. -/
@[stacks 08TC]
noncomputable def inclusion {Ksys : SequentialInverseSystem D} [HasProduct Ksys.family]
    {K K' : D} (h : HasMilnorTriangle Ksys K) (e : K ≅ K') :
    K' ⟶ ∏ᶜ Ksys.family :=
  e.inv ≫ h.ι

/-- The connecting morphism in the Milnor triangle transported along an isomorphism of its
first object. -/
@[stacks 08TC]
noncomputable def connecting {Ksys : SequentialInverseSystem D} [HasProduct Ksys.family]
    {K K' : D} (h : HasMilnorTriangle Ksys K) (e : K ≅ K') :
    ∏ᶜ Ksys.family ⟶ K'⟦(1 : ℤ)⟧ :=
  h.δ ≫ (shiftFunctor D (1 : ℤ)).map e.hom

/-- The Milnor triangle transported along an isomorphism of its first object is distinguished. -/
@[stacks 08TC]
theorem mem_distTriang {Ksys : SequentialInverseSystem D} [HasProduct Ksys.family]
    {K K' : D} (h : HasMilnorTriangle Ksys K) (e : K ≅ K') :
    Triangle.mk (inclusion h e) Ksys.milnorDifferenceMap
      (connecting h e) ∈ distTriang D := sorry

end ObjectIso

/-- Stability under isomorphism: if `K ≅ K'` and `K` has a Milnor triangle, so does `K'`. -/
@[stacks 08TC]
noncomputable def of_iso {Ksys : SequentialInverseSystem D} [HasProduct Ksys.family]
    {K K' : D} (h : HasMilnorTriangle Ksys K) (e : K ≅ K') :
    HasMilnorTriangle Ksys K' where
  ι := ObjectIso.inclusion h e
  δ := ObjectIso.connecting h e
  mem_distTriang := ObjectIso.mem_distTriang h e

/-- The first map of a Milnor triangle transported along an isomorphism is
obtained by precomposing with the inverse isomorphism. -/
@[simp, stacks 08TC]
theorem of_iso_ι {Ksys : SequentialInverseSystem D} [HasProduct Ksys.family]
    {K K' : D} (h : HasMilnorTriangle Ksys K) (e : K ≅ K') :
    (h.of_iso e).ι = e.inv ≫ h.ι := sorry

/-- The connecting map of a Milnor triangle transported along an isomorphism
is obtained by postcomposing with the shifted forward isomorphism. -/
@[simp, stacks 08TC]
theorem of_iso_δ {Ksys : SequentialInverseSystem D} [HasProduct Ksys.family]
    {K K' : D} (h : HasMilnorTriangle Ksys K) (e : K ≅ K') :
    (h.of_iso e).δ = h.δ ≫ (shiftFunctor D (1 : ℤ)).map e.hom := sorry

end HasMilnorTriangle

/-- An object `K` is a derived limit (homotopy limit) of `Ksys` when the product `∏ Kₙ`
exists and there is a Milnor distinguished triangle. -/
@[stacks 08TC]
structure IsDerivedLimit (Ksys : SequentialInverseSystem D) (K : D) where
  /-- The product of the family exists. -/
  hasProduct : HasProduct Ksys.family
  /-- The Milnor triangle data. -/
  milnor : letI := hasProduct; HasMilnorTriangle Ksys K

namespace IsDerivedLimit

/-- Extract the inclusion morphism from a derived limit. -/
noncomputable def ι {Ksys : SequentialInverseSystem D} {K : D}
    (h : IsDerivedLimit Ksys K) : letI := h.hasProduct; K ⟶ ∏ᶜ Ksys.family :=
  letI := h.hasProduct; h.milnor.ι

/-- Stability under isomorphism. -/
@[stacks 08TC]
noncomputable def of_iso {Ksys : SequentialInverseSystem D} {K K' : D}
    (h : IsDerivedLimit Ksys K) (e : K ≅ K') :
    IsDerivedLimit Ksys K' where
  hasProduct := h.hasProduct
  milnor := letI := h.hasProduct; h.milnor.of_iso e

/-- A stage comparison: the derived limit projects to each stage via the product projection. -/
@[stacks 08TC]
noncomputable def stageProjection {Ksys : SequentialInverseSystem D} {K : D}
    (h : IsDerivedLimit Ksys K) (n : ℕ) : K ⟶ Ksys.obj (op n) :=
  letI := h.hasProduct; h.ι ≫ Pi.π Ksys.family n

/-- A comparison from `X` to a derived limit of `Ksys`, specified by its composites
with the canonical stage projections.  Carrying the chosen `IsDerivedLimit` avoids forcing each
consumer to select a product presentation again. -/
@[stacks 08TC]
structure Comparison (Ksys : SequentialInverseSystem D) {X L : D}
    (c : X ⟶ L) (stageMap : ∀ n : ℕ, X ⟶ Ksys.obj (op n)) where
  /-- The chosen derived-limit presentation of the target. -/
  derivedLimit : IsDerivedLimit Ksys L
  /-- The comparison recovers the prescribed map to each stage. -/
  comp_stageProjection (n : ℕ) :
    c ≫ derivedLimit.stageProjection n = stageMap n

/-- A morphism to a chosen derived limit induces a comparison whose stage maps are its
composites with the derived-limit projections. -/
noncomputable def Comparison.ofDerivedLimit {Ksys : SequentialInverseSystem D} {X L : D}
    (h : IsDerivedLimit Ksys L) (c : X ⟶ L) :
    Comparison Ksys c (fun n => c ≫ h.stageProjection n) where
  derivedLimit := h
  comp_stageProjection := fun n => rfl

end IsDerivedLimit

end

end CategoryTheory
