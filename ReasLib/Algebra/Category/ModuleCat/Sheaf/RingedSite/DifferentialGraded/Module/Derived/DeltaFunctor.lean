/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.MappingCone.Functoriality
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Derived.Limits
public import ReasLib.CategoryTheory.Pretriangulated.DeltaFunctor.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The delta functor of differential graded module sheaves

For a short exact sequence of differential graded module sheaves, the projection from the
mapping cone of the first map to the third term is a quasi-isomorphism.  Inverting that map in
the intrinsic DG derived category gives the canonical connecting morphism.  This stays in the
single DG direction; it does not replace DG modules by cochain complexes of DG modules.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

namespace SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.Delta

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O : Sheaf J CommRingCat.{max u v}} {A : DGA(O)}

/-- The canonical map from the mapping cone of the first arrow of a short complex to its third
object.  Degreewise, it is the first projection followed by the second arrow. -/
noncomputable def coneProjection (S : ShortComplex Mod(A, d)) :
    mappingCone S.f ⟶ S.X₃ where
  toCochainMap :=
    { f := fun n ↦
        eqToHom (mappingCone_X S.f n) ≫ biprod.fst ≫ S.g.toCochainMap.f n
      comm' := sorry }
  comm := sorry

/-- The degreewise map of `coneProjection` is the first biproduct projection followed by the
second arrow of the short complex. -/
@[simp]
theorem coneProjection_f (S : ShortComplex Mod(A, d)) (n : ℤ) :
    (coneProjection S).toCochainMap.f n =
      eqToHom (mappingCone_X S.f n) ≫ biprod.fst ≫ S.g.toCochainMap.f n := sorry

/-- The mapping-cone inclusion followed by the cone projection is the second arrow of the short
complex. -/
@[reassoc]
theorem inr_coneProjection (S : ShortComplex Mod(A, d)) :
    MappingCone.inr S.f ≫ coneProjection S = S.g := sorry

/-- Cone projection is natural in morphisms of short complexes. -/
theorem coneProjection_naturality
    {S T : ShortComplex Mod(A, d)} (f : S ⟶ T) :
    MappingCone.map (f := S.f) (g := T.f) (a := f.τ₁) (b := f.τ₂)
        (CommSq.mk f.comm₁₂.symm) ≫ coneProjection T =
      coneProjection S ≫ f.τ₃ := sorry

/-- For a short exact sequence, the cone projection is a quasi-isomorphism of differential
graded module sheaves. -/
theorem coneProjection_quasiIso (S : ShortComplex Mod(A, d)) (hS : S.ShortExact) :
    Module.quasiIso A (coneProjection S) := sorry

/-- The canonical isomorphism from the mapping cone to the third term after DG localization. -/
noncomputable def coneIso (S : ShortComplex Mod(A, d)) (hS : S.ShortExact) :
    (Q A).obj (mappingCone S.f) ≅ (Q A).obj S.X₃ :=
  Localization.isoOfHom (Q A) (Module.quasiIso A) (coneProjection S)
    (coneProjection_quasiIso S hS)

/-- The forward map of `coneIso` is the localized cone projection. -/
@[simp]
theorem coneIso_hom (S : ShortComplex Mod(A, d)) (hS : S.ShortExact) :
    (coneIso S hS).hom = (Q A).map (coneProjection S) := sorry

/-- Lemma 24.27.1 (0FTB): the connecting morphism is the inverse cone comparison followed by
the mapping-cone projection to the shift of the first term. -/
@[stacks 0FTB "connecting morphism for DG module sheaves"]
noncomputable def δ (S : ShortComplex Mod(A, d)) (hS : S.ShortExact) :
    (Q A).obj S.X₃ ⟶ ((Q A).obj S.X₁)⟦(1 : ℤ)⟧ :=
  (coneIso S hS).inv ≫
    (Q A).map (MappingCone.toShift S.f) ≫
      ((Q A).commShiftIso (1 : ℤ)).hom.app S.X₁

/-- Precomposing the connecting morphism with the cone comparison recovers the localized third
map of the mapping-cone triangle. -/
@[reassoc]
theorem coneIso_hom_δ (S : ShortComplex Mod(A, d)) (hS : S.ShortExact) :
    (coneIso S hS).hom ≫ δ S hS =
      (Q A).map (MappingCone.toShift S.f) ≫
        ((Q A).commShiftIso (1 : ℤ)).hom.app S.X₁ := sorry

/-- The canonical triangle attached to a short exact sequence of DG module sheaves. -/
noncomputable def triangle (S : ShortComplex Mod(A, d)) (hS : S.ShortExact) :
    Triangle (DerivedCategory A) :=
  Triangle.mk ((Q A).map S.f) ((Q A).map S.g) (δ S hS)

/-- The canonical triangle of a short exact sequence of DG module sheaves is distinguished. -/
theorem triangle_distinguished (S : ShortComplex Mod(A, d)) (hS : S.ShortExact) :
    triangle S hS ∈ distTriang (DerivedCategory A) := sorry

/-- Connecting morphisms are natural in maps of short exact sequences. -/
theorem δ_naturality {S T : ShortComplex Mod(A, d)}
    (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T) :
    CommSq ((Q A).map f.τ₃) (δ S hS) (δ T hT)
      (((Q A).map f.τ₁)⟦(1 : ℤ)⟧') := sorry

/-- Lemma 24.27.1 (0FTB): localization from DG module sheaves to their intrinsic derived
category, equipped with its mapping-cone connecting morphisms. -/
@[stacks 0FTB "delta functor from DG module sheaves to the intrinsic derived category"]
noncomputable def functor (A : DGA(O)) : DeltaFunctor Mod(A, d) (DerivedCategory A) where
  toFunctor := Q A
  additive := qAdditive A
  δ := fun {S} hS ↦ δ S hS
  map_distinguished := sorry
  δ_naturality := sorry

/-- The underlying localization functor of the canonical DG delta functor preserves arbitrary
coproducts. -/
instance functor_preservesCoproducts (A : DGA(O)) (ι : Type*) :
    PreservesColimitsOfShape (Discrete ι) (functor A).toFunctor :=
  DerivedCategory.Coproduct.qPreserves A ι

/-- The underlying functor of the canonical DG delta functor is localization. -/
@[simp]
theorem functor_toFunctor (A : DGA(O)) :
    (functor A).toFunctor = Q A := sorry

/-- The boundary stored by the canonical DG delta functor is `Delta.δ`. -/
@[simp]
theorem functor_δ (A : DGA(O)) {S : ShortComplex Mod(A, d)} (hS : S.ShortExact) :
    (functor A).δ (S := S) hS = δ S hS := sorry

end SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.Delta
