module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactificationChange
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.FixedInterior
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Compactification

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace ActualCurveRefinement
variable {k : Type u} [Field k]
variable (U C : SchemeOverField k) [Curve U] [Curve C]
variable [hregular : Scheme.Regular C.left] [hprojective : Projective C.hom]
variable (j : U ⟶ C) [hopen : IsOpenImmersion j.left]
variable (P : Compactification.Of (Spec (CommRingCat.of k)) U)

include hregular hprojective hopen in
/-- The map from the regular projective completion to any proper
compactification is uniquely determined on the dense open curve. Existence
is the valuative extension at the boundary DVRs, uniqueness is separatedness.
This chooses geometry only, never a cohomology isomorphism. -/
theorem extension_existsUnique :
    ∃! f : C ⟶ P.obj.right, j ≫ f = P.obj.hom := sorry

def extension : C ⟶ P.obj.right := (extension_existsUnique U C j P).exists.choose

theorem extension_spec : j ≫ extension U C j P = P.obj.hom :=
  (extension_existsUnique U C j P).exists.choose_spec

/-- The extension is proper since the source is proper and the target separated over k. -/
instance extension_proper : IsProper (extension U C j P).left := sorry

/-- A proper map from the dense regular completion is an isomorphism over
the common open interior. The cartesian condition excludes boundary points
mapping spuriously into the interior. -/
theorem interior_cartesian :
    IsPullback (𝟙 U.left) j.left (Compactification.Of.ι P) (extension U C j P).left := sorry

variable [HasSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify C.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1} (Sheaf P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [HasExt.{u + 1} (Sheaf C.left.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [∀ F : U.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [∀ F : U.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (etaleRestriction j.left).op.HasLeftKanExtension F]
variable [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (smallEtalePullback (extension U C j P).left).op.HasLeftKanExtension F]

/-- The arbitrary-compactification cohomology endpoint maps to the regular
curve model by the explicit Ext pullback and extension-by-zero mate. -/
def cohomologyMap (F : Sheaf U.left.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ) :=
  ActualCompactificationChange.cohomologyMap (Compactification.Of.ι P) j.left
    (extension U C j P).left (interior_cartesian U C j P) F i

def cohomologyEquiv (F : Sheaf U.left.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : ∀ V : U.left.Etaleᵒᵖ, ∀ s : F.obj.obj V, IsOfFinAddOrder s) (i : ℕ) :=
  ActualCompactificationChange.cohomologyEquiv (Compactification.Of.ι P) j.left
    (extension U C j P).left (interior_cartesian U C j P) F hF i

end ActualCurveRefinement
