module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials.Stalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.IdealStalk
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.Criteria
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SourceLocus
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Diagonal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.LocalCriterion
import StacksCheckRecall

/-!
# Pointwise characterizations of unramified morphisms

This file characterizes unramifiedness at a point through relative differentials, affine
closed-immersion presentations, and the diagonal morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open TopCat.Sheaf.RelativeDifferentials.Stalk
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a locally finite-type morphism to a locally Noetherian scheme, unramifiedness at a
point is equivalent to vanishing of the relative-differential stalk, to an affine
closed-immersion presentation whose defining-ideal differentials span, and to the diagonal
being a local isomorphism at that point. -/
@[stacks 024P]
theorem unramifiedAt_tfae_differentials_affinePresentation_diagonal
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f]
    (x : X) :
    List.TFAE
      [ f.UnramifiedAt x
      , IsZero (RingedSpace.stalkModuleCat (Ω[f.toShHom]) x)
      , ∃ n : ℕ, ∃ V : Y.affineOpens, ∃ U : X.affineOpens, ∃ hxU : x ∈ (U : X.Opens),
          ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : Y.Opens),
            ∃ i : (U : X.Opens).toScheme ⟶
                AffineSpace (ULift.{u} (Fin n)) (V : Y.Opens).toScheme,
              IsClosedImmersion i ∧
                let π : AffineSpace (ULift.{u} (Fin n)) (V : Y.Opens).toScheme ⟶
                    (V : Y.Opens).toScheme :=
                  AffineSpace (ULift.{u} (Fin n)) (V : Y.Opens).toScheme ↘
                    (V : Y.Opens).toScheme
                i ≫ π = f.resLE V U e ∧
                let p : AffineSpace (ULift.{u} (Fin n)) (V : Y.Opens).toScheme := i ⟨x, hxU⟩
                let I := RingedSpace.idealSheafStalkIdeal
                  (RingedSpace.Hom.kernelIdealSubobject i.toShHom) p
                let d :
                    ((AffineSpace (ULift.{u} (Fin n))
                      (V : Y.Opens).toScheme).presheaf.stalk p) →
                      RingedSpace.stalkModuleCat (Ω[π.toShHom]) p :=
                  (derivation
                    (RingedSpace.Hom.inverseImageStructureSheafHomComm π.toShHom) p).d
                Submodule.span
                    ((AffineSpace (ULift.{u} (Fin n)) (V : Y.Opens).toScheme).presheaf.stalk p)
                    (d '' (I : Set
                      ((AffineSpace (ULift.{u} (Fin n))
                        (V : Y.Opens).toScheme).presheaf.stalk p))) = ⊤
      , x ∈ (@IsOpenImmersion : MorphismProperty Scheme.{u}).sourceLocus
          (pullback.diagonal f)
      ] := sorry

end AlgebraicGeometry.Scheme.Hom
