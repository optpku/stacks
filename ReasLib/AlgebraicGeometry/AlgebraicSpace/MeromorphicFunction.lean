/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.Ring.Sheaf.Localization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StructureSheaf.CommRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SheafificationCoefficients
public import ReasLib.AlgebraicGeometry.Scheme.Module.RegularSection

/-!
# Meromorphic functions on algebraic spaces

The sheaf of meromorphic functions `𝒦_X` on the small étale site of an algebraic space `X` is
the sheafification of the objectwise localization of the universe-lifted commutative structure
sheaf at the multiplicative sets of regular sections. A meromorphic function on `X` is a global
section of `𝒦_X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A section of `𝒪_X` over a scheme `U` étale over `X` is regular when it is a regular global
function of the scheme `U`. -/
def IsRegularEtaleSection {S : Scheme.{u}} {X : AlgebraicSpace S} {U : smallEtaleSite X}
    (s : (commStructureSheafLift X).obj.obj (op U)) : Prop :=
  Scheme.IsRegularStructureSection s.down

/-- Regularity of an étale section of `𝒪_X` is scheme-theoretic regularity of the underlying
global function of `U`. -/
theorem isRegularEtaleSection_iff {S : Scheme.{u}} {X : AlgebraicSpace S} {U : smallEtaleSite X}
    (s : (commStructureSheafLift X).obj.obj (op U)) :
    IsRegularEtaleSection s ↔ Scheme.IsRegularStructureSection s.down :=
  sorry

/-- The unit section of the structure sheaf on an étale chart is regular. -/
theorem isRegularEtaleSection_one {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallEtaleSite X) :
    IsRegularEtaleSection (1 : (commStructureSheafLift X).obj.obj (op U)) :=
  sorry

/-- The product of two regular structure sections on an étale chart is regular. -/
theorem isRegularEtaleSection_mul {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : smallEtaleSite X} {s t : (commStructureSheafLift X).obj.obj (op U)}
    (hs : IsRegularEtaleSection s) (ht : IsRegularEtaleSection t) :
    IsRegularEtaleSection (s * t) :=
  sorry

/-- Restriction along a morphism of étale charts preserves regular structure sections. -/
theorem isRegularEtaleSection_map {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U V : smallEtaleSite X} (f : U ⟶ V)
    {s : (commStructureSheafLift X).obj.obj (op V)} (hs : IsRegularEtaleSection s) :
    IsRegularEtaleSection (((commStructureSheafLift X).obj.map f.op).hom s) :=
  sorry

/-- The compatible family `S_X` of multiplicative sets of regular sections of `𝒪_X` on the small
étale site. -/
def regularStructureSections {S : Scheme.{u}} (X : AlgebraicSpace S) :
    CategoryTheory.Presheaf.SubmonoidPresheaf (commStructureSheafLift X).obj :=
  CategoryTheory.Presheaf.SubmonoidPresheaf.mk
    (fun U ↦
      { carrier := {s | IsRegularEtaleSection s}
        one_mem' := isRegularEtaleSection_one U.unop
        mul_mem' := fun hs ht ↦ isRegularEtaleSection_mul hs ht })
    (fun {_ _} f _ hs ↦ isRegularEtaleSection_map f.unop hs)

/-- Membership in `S_X(U)` is regularity of the corresponding étale section of `𝒪_X`. -/
theorem mem_regularStructureSections_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : smallEtaleSite X} (s : (commStructureSheafLift X).obj.obj (op U)) :
    s ∈ (regularStructureSections X).obj (op U) ↔ IsRegularEtaleSection s :=
  sorry

/-- The sheaf of meromorphic functions `𝒦_X` on `X_étale`, obtained by sheafifying the
objectwise localization `U ↦ S_X(U)⁻¹ 𝒪_X(U)`. -/
def meromorphicFunctionSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u + 1} :=
  (regularStructureSections X).localizationSheaf

/-- `𝒦_X` is the localization sheaf of `𝒪_X` at the family of regular sections. -/
theorem meromorphicFunctionSheaf_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    meromorphicFunctionSheaf X = (regularStructureSections X).localizationSheaf :=
  sorry

/-- The canonical morphism of sheaves of rings `𝒪_X ⟶ 𝒦_X`. -/
def toMeromorphicFunctionSheafHom {S : Scheme.{u}} (X : AlgebraicSpace S) :
    commStructureSheafLift X ⟶ meromorphicFunctionSheaf X :=
  (regularStructureSections X).toLocalizationSheaf

/-- The canonical map `𝒪_X ⟶ 𝒦_X` is the localization-sheaf unit. -/
theorem toMeromorphicFunctionSheafHom_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    toMeromorphicFunctionSheafHom X = (regularStructureSections X).toLocalizationSheaf :=
  sorry

/-- The ring of meromorphic functions on `X` is the ring of global sections of `𝒦_X`. -/
def meromorphicFunctions {S : Scheme.{u}} (X : AlgebraicSpace S) : CommRingCat.{u + 1} :=
  limit (meromorphicFunctionSheaf X).obj

/-- Meromorphic functions on `X` are the limit of the underlying presheaf of `𝒦_X`. -/
theorem meromorphicFunctions_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    meromorphicFunctions X = limit (meromorphicFunctionSheaf X).obj :=
  sorry

/-- The canonical ring map from global regular functions to meromorphic functions. -/
def toMeromorphicFunctions {S : Scheme.{u}} (X : AlgebraicSpace S) :
    limit (commStructureSheafLift X).obj ⟶ meromorphicFunctions X :=
  limMap (toMeromorphicFunctionSheafHom X).hom

/-- The global regular-to-meromorphic map is induced by `𝒪_X ⟶ 𝒦_X`. -/
theorem toMeromorphicFunctions_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    toMeromorphicFunctions X = limMap (toMeromorphicFunctionSheafHom X).hom :=
  sorry

/-- Local sections of `𝒦_X` are algebras over the corresponding sections of `𝒪_X`. -/
instance instAlgebraSectionsMeromorphicFunctionSheaf {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : (smallEtaleSite X)ᵒᵖ) :
    Algebra ((commStructureSheafLift X).obj.obj U)
      ((meromorphicFunctionSheaf X).obj.obj U) :=
  RingHom.toAlgebra (((toMeromorphicFunctionSheafHom X).hom.app U).hom)

end AlgebraicGeometry.AlgebraicSpace
