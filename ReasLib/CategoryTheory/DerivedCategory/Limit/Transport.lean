module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.Uniqueness
public import ReasLib.CategoryTheory.InverseSystem.Milnor.Transport
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Transport of Sequential Derived Limits

An isomorphism of sequential inverse systems transports Milnor triangles,
derived-limit presentations, and compatible comparison data. The product of
the target tower is obtained canonically from the product stored by the source
presentation; no ambient countable-product assumption is required.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

noncomputable section

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

namespace HasMilnorTriangle

namespace TowerIso

/-- The first map of a Milnor triangle after transporting its tower along an
isomorphism of sequential inverse systems. -/
noncomputable def inclusion {Ksys Lsys : SequentialInverseSystem D}
    [HasProduct Ksys.family] [HasProduct Lsys.family] {K : D}
    (h : HasMilnorTriangle Ksys K) (e : Ksys ≅ Lsys) :
    K ⟶ ∏ᶜ Lsys.family :=
  h.ι ≫ (SequentialInverseSystem.productIso e).hom

/-- The connecting map of a Milnor triangle after transporting its tower along
an isomorphism of sequential inverse systems. -/
noncomputable def connecting {Ksys Lsys : SequentialInverseSystem D}
    [HasProduct Ksys.family] [HasProduct Lsys.family] {K : D}
    (h : HasMilnorTriangle Ksys K) (e : Ksys ≅ Lsys) :
    ∏ᶜ Lsys.family ⟶ K⟦(1 : ℤ)⟧ :=
  (SequentialInverseSystem.productIso e).inv ≫ h.δ

/-- Transporting both product terms of a Milnor triangle along a tower
isomorphism preserves distinguishedness. -/
@[stacks 08TC]
theorem mem_distTriang {Ksys Lsys : SequentialInverseSystem D}
    [HasProduct Ksys.family] [HasProduct Lsys.family] {K : D}
    (h : HasMilnorTriangle Ksys K) (e : Ksys ≅ Lsys) :
    Triangle.mk (inclusion h e) Lsys.milnorDifferenceMap
      (connecting h e) ∈ distTriang D := sorry

end TowerIso

/-- Stacks 08TC: a Milnor triangle transports along an isomorphism of its
sequential inverse system. -/
@[stacks 08TC]
noncomputable def ofTowerIso {Ksys Lsys : SequentialInverseSystem D}
    [HasProduct Ksys.family] [HasProduct Lsys.family] {K : D}
    (h : HasMilnorTriangle Ksys K) (e : Ksys ≅ Lsys) :
    HasMilnorTriangle Lsys K where
  ι := TowerIso.inclusion h e
  δ := TowerIso.connecting h e
  mem_distTriang := TowerIso.mem_distTriang h e

/-- The first map of the transported Milnor triangle is the original first map
followed by the canonical product isomorphism. -/
@[simp, stacks 08TC]
theorem ofTowerIso_ι {Ksys Lsys : SequentialInverseSystem D}
    [HasProduct Ksys.family] [HasProduct Lsys.family] {K : D}
    (h : HasMilnorTriangle Ksys K) (e : Ksys ≅ Lsys) :
    (h.ofTowerIso e).ι = h.ι ≫ (SequentialInverseSystem.productIso e).hom := sorry

/-- The connecting map of the transported Milnor triangle is obtained by
precomposing with the inverse product isomorphism. -/
@[simp, stacks 08TC]
theorem ofTowerIso_δ {Ksys Lsys : SequentialInverseSystem D}
    [HasProduct Ksys.family] [HasProduct Lsys.family] {K : D}
    (h : HasMilnorTriangle Ksys K) (e : Ksys ≅ Lsys) :
    (h.ofTowerIso e).δ = (SequentialInverseSystem.productIso e).inv ≫ h.δ := sorry

namespace WithMap

/-- A prescribed-map Milnor presentation transports along an isomorphism of
sequential inverse systems. -/
@[stacks 08TC]
theorem ofTowerIso {Ksys Lsys : SequentialInverseSystem D}
    [HasProduct Ksys.family] [HasProduct Lsys.family] {K : D}
    {ι : K ⟶ ∏ᶜ Ksys.family} (h : WithMap Ksys ι) (e : Ksys ≅ Lsys) :
    WithMap Lsys (ι ≫ (SequentialInverseSystem.productIso e).hom) := sorry

end WithMap

end HasMilnorTriangle

namespace IsDerivedLimit

/-- Stacks 08TC: a derived-limit presentation transports along an isomorphism
of sequential inverse systems. The target product witness is constructed from
the source presentation and the given tower isomorphism. -/
@[stacks 08TC]
noncomputable def ofTowerIso {Ksys Lsys : SequentialInverseSystem D} {K : D}
    (h : IsDerivedLimit Ksys K) (e : Ksys ≅ Lsys) :
    IsDerivedLimit Lsys K :=
  letI : HasProduct Ksys.family := h.hasProduct
  let targetProduct : HasProduct Lsys.family :=
    SequentialInverseSystem.hasProductOfIso e
  { hasProduct := targetProduct
    milnor :=
      letI : HasProduct Lsys.family := targetProduct
      h.milnor.ofTowerIso e }

/-- Stage projections of a transported derived limit are the original stage
projections followed by the components of the tower isomorphism. -/
@[simp, stacks 08TC]
theorem ofTowerIso_stageProjection {Ksys Lsys : SequentialInverseSystem D} {K : D}
    (h : IsDerivedLimit Ksys K) (e : Ksys ≅ Lsys) (n : ℕ) :
    (h.ofTowerIso e).stageProjection n =
      h.stageProjection n ≫ e.hom.app (op n) := sorry

namespace TowerIso

/-- Derived limits of isomorphic sequential inverse systems are isomorphic by
an isomorphism compatible with the transported stage projections. -/
@[stacks 08TC]
theorem existsIsoOverStages
    {Ksys Lsys : SequentialInverseSystem D} {K L : D}
    (hK : IsDerivedLimit Ksys K) (hL : IsDerivedLimit Lsys L)
    (e : Ksys ≅ Lsys) :
    ∃ f : K ≅ L, ∀ n : ℕ,
      f.hom ≫ hL.stageProjection n =
        hK.stageProjection n ≫ e.hom.app (op n) := sorry

end TowerIso

namespace Comparison

/-- The stage equation used to transport compatible derived-limit comparison
data along an isomorphism of sequential inverse systems. -/
@[stacks 08TC]
theorem ofTowerIso_comp_stageProjection
    {Ksys Lsys : SequentialInverseSystem D} {X L : D}
    {c : X ⟶ L} {stageMap : ∀ n : ℕ, X ⟶ Ksys.obj (op n)}
    (h : Comparison Ksys c stageMap) (e : Ksys ≅ Lsys) (n : ℕ) :
    c ≫ (h.derivedLimit.ofTowerIso e).stageProjection n =
      stageMap n ≫ e.hom.app (op n) := sorry

/-- Compatible comparison data transports along an isomorphism of sequential
inverse systems, with the stage maps transported componentwise. -/
@[stacks 08TC]
noncomputable def ofTowerIso
    {Ksys Lsys : SequentialInverseSystem D} {X L : D}
    {c : X ⟶ L} {stageMap : ∀ n : ℕ, X ⟶ Ksys.obj (op n)}
    (h : Comparison Ksys c stageMap) (e : Ksys ≅ Lsys) :
    Comparison Lsys c (fun n ↦ stageMap n ≫ e.hom.app (op n)) where
  derivedLimit := h.derivedLimit.ofTowerIso e
  comp_stageProjection := ofTowerIso_comp_stageProjection h e

/-- The derived-limit presentation stored by transported comparison data is
the transport of the original presentation. -/
@[simp, stacks 08TC]
theorem ofTowerIso_derivedLimit
    {Ksys Lsys : SequentialInverseSystem D} {X L : D}
    {c : X ⟶ L} {stageMap : ∀ n : ℕ, X ⟶ Ksys.obj (op n)}
    (h : Comparison Ksys c stageMap) (e : Ksys ≅ Lsys) :
    (h.ofTowerIso e).derivedLimit = h.derivedLimit.ofTowerIso e := sorry

end Comparison

end IsDerivedLimit

end

end CategoryTheory
