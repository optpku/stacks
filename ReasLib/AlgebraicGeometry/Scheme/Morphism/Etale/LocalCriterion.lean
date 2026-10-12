/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.StandardEtale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.LocalCriterion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.LocalCriterion

/-!
# Local criteria for etale morphisms

This module characterizes etaleness at a point using flatness of the stalk map, the residue
fibre, relative differentials, and standard affine presentations.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The stalk map is flat and the residue fibre is etale at the point induced by the source
point. -/
def flatStalkMapAndEtaleFiberAt
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  (f.stalkMap x).hom.Flat ∧
    (f.fiberToSpecResidueField (f x)).EtaleAt (f.asFiber x)

/-- The stalk map is flat and the residue fibre is unramified at the point induced by the source
point. -/
def flatStalkMapAndUnramifiedFiberAt
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  (f.stalkMap x).hom.Flat ∧
    (f.fiberToSpecResidueField (f x)).UnramifiedAt (f.asFiber x)

/-- The stalk map is flat and the stalk of relative differentials vanishes at the source
point. -/
def flatStalkMapAndDifferentialsVanishAt
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  (f.stalkMap x).hom.Flat ∧
    IsZero (RingedSpace.stalkModuleCat (Ω[f.toShHom]) x)

/-- The stalk map is flat and the relative cotangent space vanishes at the source point. This
cotangent space is canonically identified with the one obtained from the residue fibre. -/
def flatStalkMapAndCotangentSpaceVanishAt
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  (f.stalkMap x).hom.Flat ∧
    Subsingleton
      (IsLocalRing.ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x]
        RingedSpace.stalkModuleCat (Ω[f.toShHom]) x)

/-- The stalk map is flat, the extended maximal ideal is the maximal ideal of the source stalk,
and the induced residue-field extension is finite and separable. -/
def flatStalkMapAndMaximalIdealResidueFieldAt
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  (f.stalkMap x).hom.Flat ∧
    MaximalIdealResidueFieldUnramifiedAtCriterion f x

/-- There are compatible affine neighbourhoods of a point and its image whose coordinate-ring
map is standard smooth of relative dimension zero. -/
def existsAffineOpenStandardSmoothRelativeDimensionZeroAt
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
    ∃ V : S.affineOpens,
      ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
        RingHom.IsStandardSmoothOfRelativeDimension 0
          (f.appLE (V : S.Opens) (U : X.Opens) e).hom

/-- There are compatible affine neighbourhoods carrying a square presentation whose selected
Jacobian determinant avoids the prime corresponding to the source point. -/
def existsAffineOpenJacobianPresentationRelativeDimensionZeroAt
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  ∃ U : X.affineOpens, ∃ hxU : x ∈ (U : X.Opens),
    ∃ V : S.affineOpens,
      ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
        ∃ n : ℕ,
          ∃ P : Algebra.PreSubmersivePresentation
              Γ(S, (V : S.Opens))
              (f.sectionsAlg (V : S.Opens) (U : X.Opens) e) (Fin n) (Fin n),
            P.jacobian ∉ (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal

/-- There are compatible affine neighbourhoods carrying a monic one-variable standard-etale
presentation whose polynomial derivative avoids the prime corresponding to the source point. -/
def existsAffineOpenStandardEtalePresentationAt
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  ∃ U : X.affineOpens, ∃ hxU : x ∈ (U : X.Opens),
    ∃ V : S.affineOpens,
      ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
        ∃ P : StandardEtalePresentation
            Γ(S, (V : S.Opens)) (f.sectionsAlg (V : S.Opens) (U : X.Opens) e),
          Polynomial.aeval P.x P.f.derivative ∉ (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal

/-- For a locally finitely presented morphism, etaleness at a point is equivalent to flatness
of the stalk map together with any of the residue-fibre, differential, cotangent-space, or
residue-field conditions, and to any of four standard affine presentation conditions. -/
theorem etaleAt_tfae_flat_stalkMap_fiber_differentials_standardEtale
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (x : X) :
    List.TFAE
      [ f.EtaleAt x
      , flatStalkMapAndEtaleFiberAt f x
      , flatStalkMapAndUnramifiedFiberAt f x
      , flatStalkMapAndDifferentialsVanishAt f x
      , flatStalkMapAndCotangentSpaceVanishAt f x
      , flatStalkMapAndMaximalIdealResidueFieldAt f x
      , existsAffineOpenStandardSmoothRelativeDimensionZeroAt f x
      , existsAffineOpenJacobianPresentationRelativeDimensionZeroAt f x
      , ∃ V : S.affineOpens, f x ∈ (V : S.Opens) ∧
          ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
            f.IsStandardEtaleOver V U
      , existsAffineOpenStandardEtalePresentationAt f x
      ] := sorry

end AlgebraicGeometry.Scheme.Hom
