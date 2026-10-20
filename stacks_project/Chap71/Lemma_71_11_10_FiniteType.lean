module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.FiniteType

/-!
# Affine-étale finiteness and projective-spectrum presentations

Typed checks retain access to the canonical mathematical owners for chapter consumers.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj SheafOfModules.RingedSite

universe u

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.IsEtaleLocallyProj :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} →
    GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X) →
    {P : AlgebraicSpace S} → (P ⟶ X) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.FiniteTypeAsDegreeZeroAlgebra :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} →
    GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.FiniteTypeAsBaseAlgebra :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} →
    GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X) → Prop)
