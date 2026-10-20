module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Stein.Normal
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.36.6. A proper morphism from a reduced algebraic space to an integral
normal algebraic space, whose generic points dominate and whose generic fibre has
only the residue field as global sections, induces an isomorphism on the structure
sheaf direct image and has geometrically connected fibres. -/
@[stacks 0AYI] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.structureSheaf_and_connectedFibres :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Proper f] [IsIntegral Y] [IsNormal Y] [IsReduced X]
      {ξ : Points Y} (hξ : ξ ∈ genericPoints Y)
      (h_generic : ∀ ⦃x : Points X⦄, x ∈ genericPoints X → Points.map f x = ξ)
      (hΓ : IsIso (AlgebraicGeometry.AlgebraicSpace.Hom.genericFiberGlobalSectionsMap f ξ)),
      IsIso (AlgebraicGeometry.AlgebraicSpace.commStructureSheafMap f) ∧
        AlgebraicGeometry.AlgebraicSpace.HasConnectedGeometricFibres f)
