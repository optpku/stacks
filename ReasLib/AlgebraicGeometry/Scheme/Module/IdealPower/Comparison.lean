/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Cover
public import ReasLib.CategoryTheory.Functor.OfSequence.Colimit
public import ReasLib.Topology.Sheaves.Glue

/-!
# Linear comparisons on finite basic-open covers

This leaf owns the common glue-and-colimit construction used by ideal-power
Hom systems.  A concrete local-fraction formula belongs to the consumer leaf;
the finite-cover, linear, and sequential-colimit plumbing belongs here.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open AlgebraicGeometry PrimeSpectrum
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- Stage data for a linear comparison over the basic-open cover determined by `G`. -/
structure IdealComplementStage (G : I.FiniteGeneratingFamily) (M : ModuleCat.{u} A) where
  /-- The `A`-module at each stage. -/
  stage : ℕ → ModuleCat.{u} A
  /-- The transition from stage `n` to stage `n + 1`. -/
  transition : ∀ n, stage n ⟶ stage (n + 1)
  /-- The local section attached to an element at each basic open. -/
  localSection : ∀ (n : ℕ), (x : stage n) → ∀ i : G.Index,
    ((tildePresheaf M).obj (Opposite.op (G.basicOpen i)) : Type u)
  /-- The local sections satisfy the sheaf compatibility condition. -/
  compatible : ∀ (n : ℕ) (x : stage n),
    TopCat.Presheaf.IsCompatible
      (tildePresheaf M)
      G.basicOpen
      (localSection n x)

namespace IdealComplementStage

variable {G : I.FiniteGeneratingFamily} {M : ModuleCat.{u} A}

/-- The chosen global section obtained by gluing the local sections of a stage. -/
noncomputable def gluedSection (C : IdealComplementStage G M) (n : ℕ)
    (x : C.stage n) : idealComplementTildeSections I M :=
  (tildeSheaf M).glueOfCompatibleFamily
    G.basicOpen
    (idealComplementOpens I)
    (fun i ↦ homOfLE (G.basicOpen_le_idealComplementOpens i))
    G.idealComplementOpens_le_iSup_basicOpen
    (C.localSection n x)
    (C.compatible n x)

/-- Restriction of the chosen global section recovers its local section. -/
theorem gluedSection_spec (C : IdealComplementStage G M) (n : ℕ)
    (x : C.stage n) (i : G.Index) :
    (tildePresheaf M).map (homOfLE (G.basicOpen_le_idealComplementOpens i)).op
        (C.gluedSection n x) =
      C.localSection n x i := sorry

end IdealComplementStage

variable {G : I.FiniteGeneratingFamily} {M : ModuleCat.{u} A}

/-- The property that the canonical glued sections of a stage system are linear and commute with
its transition maps.  It is a proposition: the global sections themselves are already owned by
`IdealComplementStage.gluedSection`. -/
def IdealComplementStage.IsLinear (C : IdealComplementStage G M) : Prop :=
  (∀ (n : ℕ), C.gluedSection n (0 : C.stage n) = 0) ∧
  (∀ (n : ℕ) (x y : C.stage n),
    C.gluedSection n (x + y) = C.gluedSection n x + C.gluedSection n y) ∧
  (∀ (n : ℕ) (a : A) (x : C.stage n),
    C.gluedSection n (((C.stage n).smul a).hom x) =
      ((idealComplementTildeSections I M).smul a).hom (C.gluedSection n x)) ∧
  (∀ (n : ℕ) (x : C.stage n),
    C.gluedSection (n + 1) ((C.transition n).hom x) = C.gluedSection n x)

namespace IdealComplementStage.IsLinear

variable {G : I.FiniteGeneratingFamily} {M : ModuleCat.{u} A}

/-- A linear stage system sends zero to the zero section at every stage. -/
theorem section_zero {C : IdealComplementStage G M} (hC : C.IsLinear) (n : ℕ) :
    C.gluedSection n (0 : C.stage n) = 0 := sorry

/-- A linear stage system sends sums to sums of sections at every stage. -/
theorem section_add {C : IdealComplementStage G M} (hC : C.IsLinear)
    (n : ℕ) (x y : C.stage n) :
    C.gluedSection n (x + y) = C.gluedSection n x + C.gluedSection n y := sorry

/-- A linear stage system preserves scalar multiplication at every stage. -/
theorem section_smul {C : IdealComplementStage G M} (hC : C.IsLinear)
    (n : ℕ) (a : A) (x : C.stage n) :
    C.gluedSection n (((C.stage n).smul a).hom x) =
      ((idealComplementTildeSections I M).smul a).hom (C.gluedSection n x) := sorry

/-- The sections of a linear stage system commute with its transition maps. -/
theorem section_naturality {C : IdealComplementStage G M} (hC : C.IsLinear)
    (n : ℕ) (x : C.stage n) :
    C.gluedSection (n + 1) ((C.transition n).hom x) = C.gluedSection n x := sorry

/-- The additive-group map induced by the canonical glued sections at one stage. -/
noncomputable def stageAdditiveMap (C : IdealComplementStage G M) (hC : C.IsLinear) (n : ℕ) :
    (forget₂ (ModuleCat A) AddCommGrpCat).obj (C.stage n) ⟶
      (forget₂ (ModuleCat A) AddCommGrpCat).obj (idealComplementTildeSections I M) :=
  AddCommGrpCat.ofHom
    { toFun := C.gluedSection n
      map_zero' := hC.section_zero n
      map_add' := hC.section_add n
    }

/-- The additive stage map commutes with the scalar endomorphisms of its source and target
module objects. -/
theorem stageAdditiveMap_smul (C : IdealComplementStage G M) (hC : C.IsLinear)
    (n : ℕ) (a : A) :
    stageAdditiveMap C hC n ≫ (idealComplementTildeSections I M).smul a =
      (C.stage n).smul a ≫ stageAdditiveMap C hC n := sorry

/-- The stage comparison map obtained from linear canonical glued sections. -/
noncomputable def stageMap (C : IdealComplementStage G M) (hC : C.IsLinear) (n : ℕ) :
    C.stage n ⟶ idealComplementTildeSections I M :=
  ModuleCat.homMk
    (stageAdditiveMap C hC n)
    (fun a ↦ stageAdditiveMap_smul C hC n a)

/-- The stage comparison maps commute with the transition maps. -/
theorem stageMap_naturality (C : IdealComplementStage G M) (hC : C.IsLinear) (n : ℕ) :
    C.transition n ≫ stageMap C hC (n + 1) = stageMap C hC n := sorry

/-- The comparison map from the sequential colimit of the stages to sections on the ideal
complement. -/
noncomputable def colimitMap (C : IdealComplementStage G M) (hC : C.IsLinear) :
    colimit (Functor.ofSequence C.transition) ⟶ idealComplementTildeSections I M :=
  Functor.ofSequence.colimitDesc
    C.transition
    (stageMap C hC)
    (stageMap_naturality C hC)

/-- The colimit comparison map restricts to its stage map on every inclusion. -/
@[reassoc]
theorem colimitMap_ι (C : IdealComplementStage G M) (hC : C.IsLinear) (n : ℕ) :
    colimit.ι (Functor.ofSequence C.transition) n ≫ colimitMap C hC = stageMap C hC n := sorry

end IdealComplementStage.IsLinear

end AlgebraicGeometry.Scheme.Modules
