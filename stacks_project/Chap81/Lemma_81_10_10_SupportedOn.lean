/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Definition_75_3_2_SupportedOn

/-!
# Derived quasi-coherent modules supported on a subset

`DerivedQCoh.SupportedOn X T` is the full subcategory of `D(𝒪_X)` on complexes
with quasi-coherent cohomology supported on `T ⊆ Points X`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- The object property of derived `𝒪_X`-modules with quasi-coherent cohomology
supported on `T`. -/
abbrev quasiCoherentSupportedOn {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Set (Points X)) : ObjectProperty (ModuleDerived X) :=
  fun E ↦ derivedQuasiCoherentModuleProperty X E ∧ ModuleDerived.IsSupportedOn E T

/-- The derived category `D_{QCoh, T}(𝒪_X)` of complexes with quasi-coherent
cohomology supported on `T`. -/
abbrev SupportedOn {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Set (Points X)) :=
  (quasiCoherentSupportedOn X T).FullSubcategory

namespace SupportedOn

/-- Membership in `quasiCoherentSupportedOn` is quasi-coherence of cohomology
together with support on `T`. -/
theorem mem_iff {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Set (Points X)}
    (E : ModuleDerived X) :
    quasiCoherentSupportedOn X T E ↔
      derivedQuasiCoherentModuleProperty X E ∧ ModuleDerived.IsSupportedOn E T :=
  sorry

/-- The inclusion of `SupportedOn X T` into `DerivedQCoh X`. -/
def inclusion {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Set (Points X)) :
    SupportedOn X T ⥤ DerivedQCoh X :=
  ObjectProperty.ιOfLE (fun _ hE ↦ hE.left)

/-- The underlying object of the inclusion into `DerivedQCoh` is the same derived
module. -/
theorem inclusion_obj_obj {S : Scheme.{u}} {X : AlgebraicSpace S}
    {T : Set (Points X)} (K : SupportedOn X T) :
    ((inclusion X T).obj K).obj = K.obj :=
  sorry

/-- Package a derived quasi-coherent complex together with a support condition. -/
def mk {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Set (Points X)}
    (E : DerivedQCoh X) (h : ModuleDerived.IsSupportedOn E.obj T) :
    SupportedOn X T :=
  ⟨E.obj, ⟨E.property, h⟩⟩

/-- An object of `SupportedOn X T` has quasi-coherent cohomology and is supported
on `T`. -/
theorem obj_properties {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Set (Points X)}
    (K : SupportedOn X T) :
    derivedQuasiCoherentModuleProperty X K.obj ∧ ModuleDerived.IsSupportedOn K.obj T :=
  sorry

end SupportedOn

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
