/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Abelian
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Hom
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.FromModules
public import ReasLib.Algebra.Homology.DifferentialGradedModule.MappingCone.Triangle
public import ReasLib.CategoryTheory.Pretriangulated.DeltaFunctor.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The Delta Functor to the Derived Category of a DG Algebra

An arbitrary short exact sequence of right differential graded modules is compared with the
mapping cone of its first map.  The cone-to-quotient comparison is a quasi-isomorphism, so its
inverse after localization gives the canonical connecting morphism.  The resulting construction
packages `DifferentialGradedModule.Derived.fromModules` as a reusable `DeltaFunctor`.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Pretriangulated DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedModule.Derived.Delta

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable (S : ShortComplex (DifferentialGradedModule.{u, v} A))

/-- The canonical map from the mapping cone of the first arrow of a short complex to its third
object.  In degree `n` it is projection to `S.X₂.X n` followed by `S.g`. -/
def coneProjection : mappingCone S.f ⟶ S.X₃ where
  hom n := (S.g.hom n).comp (LinearMap.fst R (S.X₂.X n) (S.X₁.X (n + 1)))
  comm_d := sorry
  comm_smul := sorry

/-- The cone projection is degreewise the first coordinate followed by the second arrow of the
short complex. -/
@[simp]
theorem coneProjection_hom (n : ℤ) :
    (coneProjection S).hom n =
      (S.g.hom n).comp (LinearMap.fst R (S.X₂.X n) (S.X₁.X (n + 1))) := sorry

/-- The mapping-cone inclusion followed by the cone projection is the second arrow of the short
complex. -/
@[reassoc]
theorem inclusion_coneProjection :
    MappingCone.inclusion S.f ≫ coneProjection S = S.g := sorry

/-- Cone projection is natural in morphisms of short complexes. -/
theorem coneProjection_naturality
    {T : ShortComplex (DifferentialGradedModule.{u, v} A)} (φ : S ⟶ T) :
    MappingCone.map φ.τ₁ φ.τ₂ φ.comm₁₂.symm ≫ coneProjection T =
      coneProjection S ≫ φ.τ₃ := sorry

/-- For a short exact sequence, the cone projection is a quasi-isomorphism in the intrinsic DG
homotopy category. -/
theorem coneProjection_quasiIso (hS : S.ShortExact) :
    quasiIso A ((toK A).map (coneProjection S)) := sorry

/-- The canonical comparison between the mapping cone and the quotient term of a short exact
sequence after localization. -/
noncomputable def coneIso (hS : S.ShortExact) :
    (fromModules A).obj (mappingCone S.f) ≅ (fromModules A).obj S.X₃ :=
  Localization.isoOfHom (Q A) (quasiIso A) ((toK A).map (coneProjection S))
    (coneProjection_quasiIso S hS)

/-- The forward map of the localized cone comparison is the derived image of the cone
projection. -/
@[simp]
theorem coneIso_hom (hS : S.ShortExact) :
    (coneIso S hS).hom = (fromModules A).map (coneProjection S) := sorry

/-- The connecting morphism of a short exact sequence of right DG modules.  It is the inverse of
the localized cone projection followed by the third map of the mapping-cone triangle. -/
@[stacks 09L0 "connecting morphism for a short exact sequence of DG modules"]
noncomputable def δ (hS : S.ShortExact) :
    (fromModules A).obj S.X₃ ⟶ ((fromModules A).obj S.X₁)⟦(1 : ℤ)⟧ :=
  (coneIso S hS).inv ≫
    (fromModules A).map (MappingCone.toShift S.f) ≫
      (toKShiftIso S.X₁ (1 : ℤ)).hom

/-- After precomposition with the cone comparison, the connecting morphism is the third map of
the localized mapping-cone triangle. -/
@[reassoc]
theorem coneIso_hom_δ (hS : S.ShortExact) :
    (coneIso S hS).hom ≫ δ S hS =
      (fromModules A).map (MappingCone.toShift S.f) ≫
        (toKShiftIso S.X₁ (1 : ℤ)).hom := sorry

/-- The canonical triangle attached to a short exact sequence of right DG modules. -/
noncomputable def triangle (hS : S.ShortExact) : Triangle (Category A) :=
  Triangle.mk ((fromModules A).map S.f) ((fromModules A).map S.g) (δ S hS)

/-- Lemma 22.23.1 (09L0): the canonical triangle attached to a short exact sequence of right DG
modules is distinguished in the derived category. -/
@[stacks 09L0 "short exact sequences give distinguished triangles in the DG derived category"]
theorem triangle_distinguished (hS : S.ShortExact) :
    triangle S hS ∈ distTriang (Category A) := sorry

/-- Connecting morphisms of short exact DG-module sequences are natural. -/
theorem δ_naturality
    {T : ShortComplex (DifferentialGradedModule.{u, v} A)}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) :
    CommSq ((fromModules A).map φ.τ₃) (δ S hS) (δ T hT)
      (((fromModules A).map φ.τ₁)⟦(1 : ℤ)⟧') := sorry

/-- Lemma 22.23.1 (09L0): the canonical functor from right DG modules to their derived category,
with the connecting morphisms induced by mapping cones. -/
@[stacks 09L0 "delta functor from DG modules to their derived category"]
noncomputable def functor (A : CochainDGAlgebra.{u, v} R) :
    DeltaFunctor (DifferentialGradedModule.{u, v} A) (Category A) where
  toFunctor := fromModules A
  additive := inferInstance
  δ := fun {_} hS ↦ δ _ hS
  map_distinguished := sorry
  δ_naturality := sorry

/-- The underlying functor of the canonical DG-module delta functor is `fromModules A`. -/
theorem functor_toFunctor (A : CochainDGAlgebra.{u, v} R) :
    (functor A).toFunctor = fromModules A := sorry

/-- The boundary map stored by the canonical DG-module delta functor is the mapping-cone
connecting morphism `δ`. -/
theorem functor_δ (A : CochainDGAlgebra.{u, v} R)
    {S : ShortComplex (DifferentialGradedModule.{u, v} A)} (hS : S.ShortExact) :
    (functor A).δ hS = δ S hS := sorry

end DifferentialGradedModule.Derived.Delta
