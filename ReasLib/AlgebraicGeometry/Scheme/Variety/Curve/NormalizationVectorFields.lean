/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Normalization.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.VectorFields

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.Scheme.Hom
open SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

/-- The closed points of the normalization where the normalization morphism is not an isomorphism
on stalks. -/
def normalizationExceptionalPoints
    {k : Type u} [Field k] (X : SchemeOverField k) [Algebraic X] :
    Set (closedPoints (SchemeOverField.normalization X).left) :=
  let ν := X.left.normalizationTo
  {xν | ¬ IsIso (ν.stalkMap xν.1)}

/-- Membership in `normalizationExceptionalPoints` is exactly non-invertibility of the
normalization stalk map. -/
theorem normalizationExceptionalPoints_mem
    {k : Type u} [Field k] (X : SchemeOverField k) [Algebraic X]
    (xν : closedPoints (SchemeOverField.normalization X).left) :
    xν ∈ normalizationExceptionalPoints X ↔
      let ν := X.left.normalizationTo
      ¬ IsIso (ν.stalkMap xν.1) := sorry

/-- A normalized derivation extends a derivation on `X` when it commutes with the
normalization structure-sheaf map on every section. -/
def normalizationDerivationExtends
    {k : Type u} [Field k] (X : SchemeOverField k) [Algebraic X]
    (D : derivations X.hom.toShHom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules))
    (D' : derivations (SchemeOverField.normalization X).hom.toShHom
      (SheafOfModules.unit
        (SchemeOverField.normalization X).left.ringCatSheaf :
        (SchemeOverField.normalization X).left.Modules)) : Prop :=
  let Y := X.left
  let ν := Y.normalizationTo
  let φ := ν.toRingCatSheafHom
  ∀ {U : (Opens Y)ᵒᵖ} (s : Y.presheaf.obj U),
    D'.d (φ.hom.app U s) = φ.hom.app U (D.d s)

/-- An extension of a derivation to the normalization fixes every exceptional normalization point. -/
theorem normalizationDerivationExtends_fixes
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Algebraic X] [IsProper X.hom] [ConnectedSpace X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_nodal : atWorstNodal X)
    (D : derivations X.hom.toShHom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules))
    (D' : derivations (SchemeOverField.normalization X).hom.toShHom
      (SheafOfModules.unit
        (SchemeOverField.normalization X).left.ringCatSheaf :
        (SchemeOverField.normalization X).left.Modules))
    (h_extends : normalizationDerivationExtends X D D') :
    ∀ xν ∈ normalizationExceptionalPoints X,
      derivationFixesAt (SchemeOverField.normalization X) D' xν := sorry

/-- A derivation on the normalization descends exactly when it fixes every exceptional
normalization point. -/
theorem normalizationDerivation_range
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Algebraic X] [IsProper X.hom] [ConnectedSpace X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_nodal : atWorstNodal X)
    (D' : derivations (SchemeOverField.normalization X).hom.toShHom
      (SheafOfModules.unit
        (SchemeOverField.normalization X).left.ringCatSheaf :
        (SchemeOverField.normalization X).left.Modules)) :
    (∃ D : derivations X.hom.toShHom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules),
      normalizationDerivationExtends X D D') ↔
      ∀ xν ∈ normalizationExceptionalPoints X,
        derivationFixesAt (SchemeOverField.normalization X) D' xν := sorry

/-- Every normalized derivation fixing the exceptional points descends to a derivation on `X`. -/
theorem normalizationDerivation_extension_exists
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Algebraic X] [IsProper X.hom] [ConnectedSpace X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_nodal : atWorstNodal X)
    (D' : derivations (SchemeOverField.normalization X).hom.toShHom
      (SheafOfModules.unit
        (SchemeOverField.normalization X).left.ringCatSheaf :
        (SchemeOverField.normalization X).left.Modules))
    (h_fixes : ∀ xν ∈ normalizationExceptionalPoints X,
      derivationFixesAt (SchemeOverField.normalization X) D' xν) :
    ∃ D : derivations X.hom.toShHom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules),
      normalizationDerivationExtends X D D' := sorry

/-- Extensions of a normalized derivation to `X` are unique. -/
theorem normalizationDerivation_extension_unique
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Algebraic X] [IsProper X.hom] [ConnectedSpace X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_nodal : atWorstNodal X)
    (D' : derivations (SchemeOverField.normalization X).hom.toShHom
      (SheafOfModules.unit
        (SchemeOverField.normalization X).left.ringCatSheaf :
        (SchemeOverField.normalization X).left.Modules))
    {D₁ D₂ : derivations X.hom.toShHom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules)}
    (h₁ : normalizationDerivationExtends X D₁ D')
    (h₂ : normalizationDerivationExtends X D₂ D') :
    D₁ = D₂ := sorry

/-- Every derivation on a proper connected nodal curve has a unique compatible
derivation on its normalization. -/
theorem normalizationDerivation_lift_existsUnique
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Algebraic X] [IsProper X.hom] [ConnectedSpace X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_nodal : atWorstNodal X)
    (D : derivations X.hom.toShHom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules)) :
    ∃! D' : derivations (SchemeOverField.normalization X).hom.toShHom
      (SheafOfModules.unit
        (SchemeOverField.normalization X).left.ringCatSheaf :
        (SchemeOverField.normalization X).left.Modules),
      normalizationDerivationExtends X D D' := sorry

end AlgebraicGeometry.Curve
