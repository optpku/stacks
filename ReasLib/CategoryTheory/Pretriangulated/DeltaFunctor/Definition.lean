module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Delta Functors to Pretriangulated Categories

This module owns delta functors from an abelian category to a pretriangulated
category, together with the triangle attached to a short exact sequence.
Target-side exact-functor composition and the cohomological bridge live in
the sibling leaves `Composition` and `Cohomological`.
-/

@[expose] public section

namespace CategoryTheory

open Limits
open Pretriangulated

universe vA uA vD uD

variable {A : Type uA} {D : Type uD} [Category.{vA} A] [Abelian A]
  [Category.{vD} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- A `DeltaFunctor` from an abelian category `A` to a pretriangulated category `D`
is an additive functor equipped with connecting morphisms on short exact sequences
whose associated triangles are distinguished and natural in maps of short exact sequences. -/
@[stacks 0150]
structure DeltaFunctor (A : Type uA) [Category.{vA} A] [Abelian A]
    (D : Type uD) [Category.{vD} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] extends A ⥤ D where
  /-- The underlying functor is additive. -/
  additive : toFunctor.Additive
  /-- The connecting morphism attached to a short exact sequence. -/
  δ ⦃S : ShortComplex A⦄ (hS : S.ShortExact) :
    obj S.X₃ ⟶ (obj S.X₁)⟦(1 : ℤ)⟧
  /-- The triangle induced by a short exact sequence is distinguished. -/
  map_distinguished ⦃S : ShortComplex A⦄ (hS : S.ShortExact) :
    Triangle.mk (map S.f) (map S.g) (δ hS) ∈ distTriang D
  /-- Connecting morphisms commute with maps of short exact sequences. -/
  δ_naturality ⦃S T : ShortComplex A⦄ (hS : S.ShortExact) (hT : T.ShortExact)
      (φ : S ⟶ T) :
    CommSq (map φ.τ₃) (δ hS) (δ hT) ((map φ.τ₁)⟦(1 : ℤ)⟧')

namespace DeltaFunctor

variable (F : DeltaFunctor A D)

/-- The underlying additive functor of a delta functor. -/
def additiveFunctor : A ⥤+ D :=
  ⟨F.toFunctor, F.additive⟩

/-- Construct a delta functor from an additive functor, connecting morphisms, and proofs that
the resulting triangles are distinguished and natural in short exact sequences. -/
def ofAdditive
    (F : A ⥤+ D)
    (δ : ∀ ⦃S : ShortComplex A⦄ (_hS : S.ShortExact),
      F.obj.obj S.X₃ ⟶ (F.obj.obj S.X₁)⟦(1 : ℤ)⟧)
    (map_distinguished : ∀ ⦃S : ShortComplex A⦄ (hS : S.ShortExact),
      Triangle.mk (F.obj.map S.f) (F.obj.map S.g) (δ hS) ∈ distTriang D)
    (δ_naturality : ∀ ⦃S T : ShortComplex A⦄ (hS : S.ShortExact) (hT : T.ShortExact)
      (φ : S ⟶ T),
      CommSq (F.obj.map φ.τ₃) (δ hS) (δ hT) ((F.obj.map φ.τ₁)⟦(1 : ℤ)⟧')) :
    DeltaFunctor A D where
  toFunctor := F.obj
  additive := F.property
  δ := δ
  map_distinguished := map_distinguished
  δ_naturality := δ_naturality

/-- The triangle attached to a short exact sequence by a `DeltaFunctor`. -/
abbrev triangle {S : ShortComplex A} (hS : S.ShortExact) : Triangle D where
  obj₁ := F.obj S.X₁
  obj₂ := F.obj S.X₂
  obj₃ := F.obj S.X₃
  mor₁ := F.map S.f
  mor₂ := F.map S.g
  mor₃ := F.δ hS

/-- A map of short exact sequences induces a map between the associated triangles. -/
@[simps!]
def triangleMap {S T : ShortComplex A} (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) :
    F.triangle hS ⟶ F.triangle hT :=
  Triangle.homMk _ _ (F.map φ.τ₁) (F.map φ.τ₂) (F.map φ.τ₃)
    (by
      change F.map S.f ≫ F.map φ.τ₂ = F.map φ.τ₁ ≫ F.map T.f
      simpa only [Functor.map_comp] using
        congrArg (fun f ↦ F.map f) φ.comm₁₂.symm)
    (by
      change F.map S.g ≫ F.map φ.τ₃ = F.map φ.τ₂ ≫ F.map T.g
      simpa only [Functor.map_comp] using
        congrArg (fun g ↦ F.map g) φ.comm₂₃.symm)
    (by
      change F.δ hS ≫ (shiftFunctor D 1).map (F.map φ.τ₁) = F.map φ.τ₃ ≫ F.δ hT
      exact (F.δ_naturality hS hT φ).w.symm)

/-- The triangle attached to a short exact sequence is distinguished. -/
theorem triangle_distinguished {S : ShortComplex A} (hS : S.ShortExact) :
    F.triangle hS ∈ distTriang D :=
  by
    simpa [triangle, Triangle.mk] using F.map_distinguished hS

end DeltaFunctor

end CategoryTheory
