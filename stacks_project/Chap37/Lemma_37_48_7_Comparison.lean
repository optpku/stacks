module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Ph.Comparison

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

#check
  (AlgebraicGeometry.Scheme.FppfCovering.phCovering :
    ∀ {T : Scheme.{u}} {ι : Type v} {family : ι → CategoryTheory.Over T},
      AlgebraicGeometry.Scheme.FppfCovering family →
        AlgebraicGeometry.PhCovering (fun i ↦ (family i).left) (fun i ↦ (family i).hom))

#check
  (AlgebraicGeometry.FppfCover.phCovering :
    ∀ {T : Scheme.{u}} (𝒰 : AlgebraicGeometry.FppfCover.{u, v} T),
      AlgebraicGeometry.PhCovering 𝒰.X 𝒰.f)
