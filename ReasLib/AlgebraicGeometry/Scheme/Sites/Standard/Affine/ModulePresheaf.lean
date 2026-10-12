/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AffineOver

/-!
# Cartesian module presheaves on affine schemes

This module provides the topology-independent category of module presheaves on affine schemes
over a scheme and the full subcategory satisfying base-change compatibility.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Presheaf

noncomputable section

universe u

namespace AlgebraicGeometry.StandardTopology.Affine

/-- The commutative-ring presheaf of global functions on affine schemes over `S`. -/
abbrev commRingPresheaf (S : Scheme.{u}) : S.AffineOverᵒᵖ ⥤ CommRingCat.{u} :=
  (Scheme.AffineOver.toScheme S).op ⋙ Scheme.Γ

/-- The affine global-functions presheaf evaluates at the source scheme. -/
theorem commRingPresheaf_obj (S : Scheme.{u}) (U : S.AffineOver) :
    (commRingPresheaf S).obj (op U) =
      Scheme.Γ.obj (op ((Scheme.AffineOver.toScheme S).obj U)) := sorry

/-- Restriction in the affine global-functions presheaf is pullback of functions. -/
theorem commRingPresheaf_map (S : Scheme.{u}) {U V : S.AffineOver} (f : U ⟶ V) :
    (commRingPresheaf S).map f.op =
      Scheme.Γ.map ((Scheme.AffineOver.toScheme S).map f).op := sorry

/-- Presheaves of modules over the affine global-functions presheaf. -/
abbrev ModulePresheaf (S : Scheme.{u}) :=
  PresheafOfModules.{u} (ringPresheaf (commRingPresheaf S))

namespace ModulePresheaf

/-- Evaluation of an affine module presheaf on an affine scheme over `S`. -/
abbrev eval {S : Scheme.{u}} (F : ModulePresheaf S) (U : S.AffineOver) :=
  F.obj (op U)

/-- The scalar-extension comparison attached to a morphism of affine schemes over `S`. -/
noncomputable def baseChangeMap {S : Scheme.{u}} (F : ModulePresheaf S)
    {U U' : S.AffineOver} (f : U ⟶ U') :
    (PresheafOfModules.BaseChange.functor (commRingPresheaf S) f.op).obj F ⟶
      F.eval U :=
  PresheafOfModules.BaseChange.map (commRingPresheaf S) F f.op

/-- The named affine base-change map is the canonical presheaf base-change comparison. -/
theorem baseChangeMap_def {S : Scheme.{u}} (F : ModulePresheaf S)
    {U U' : S.AffineOver} (f : U ⟶ U') :
    F.baseChangeMap f =
      PresheafOfModules.BaseChange.map (commRingPresheaf S) F f.op := sorry

/-- An affine module presheaf is cartesian when every scalar-extension comparison is an
isomorphism. -/
def IsCartesian {S : Scheme.{u}} (F : ModulePresheaf S) : Prop :=
  PresheafOfModules.BaseChange.compatible (commRingPresheaf S) F

/-- Cartesianness is the pointwise isomorphism condition for affine base-change maps. -/
theorem isCartesian_iff {S : Scheme.{u}} (F : ModulePresheaf S) :
    F.IsCartesian ↔
      ∀ {U U' : S.AffineOver} (f : U ⟶ U'), IsIso (F.baseChangeMap f) := sorry

end ModulePresheaf

/-- The category of cartesian module presheaves on affine schemes over `S`. -/
abbrev CartesianModule (S : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (fun F : ModulePresheaf S ↦ F.IsCartesian)

namespace CartesianModule

/-- The inclusion of cartesian affine module presheaves into all affine module presheaves. -/
abbrev inclusion (S : Scheme.{u}) : CartesianModule S ⥤ ModulePresheaf S :=
  ObjectProperty.ι
    ((fun F : ModulePresheaf S ↦ F.IsCartesian) : ObjectProperty (ModulePresheaf S))

/-- The underlying module presheaf of a cartesian module is cartesian. -/
theorem isCartesian {S : Scheme.{u}} (F : CartesianModule S) :
    F.obj.IsCartesian := sorry

/-- Every affine base-change comparison of a cartesian module is an isomorphism. -/
instance baseChangeMap_isIso {S : Scheme.{u}} (F : CartesianModule S)
    {U U' : S.AffineOver} (f : U ⟶ U') : IsIso (F.obj.baseChangeMap f) :=
  F.property f.op

/-- The canonical scalar-extension isomorphism of a cartesian affine module. -/
noncomputable def baseChangeIso {S : Scheme.{u}} (F : CartesianModule S)
    {U U' : S.AffineOver} (f : U ⟶ U') :
    (PresheafOfModules.BaseChange.functor (commRingPresheaf S) f.op).obj F.obj ≅
      F.obj.eval U :=
  asIso (F.obj.baseChangeMap f)

/-- The forward map of the cartesian base-change isomorphism is the canonical comparison. -/
theorem baseChangeIso_hom {S : Scheme.{u}} (F : CartesianModule S)
    {U U' : S.AffineOver} (f : U ⟶ U') :
    (F.baseChangeIso f).hom = F.obj.baseChangeMap f := sorry

end CartesianModule

end AlgebraicGeometry.StandardTopology.Affine
