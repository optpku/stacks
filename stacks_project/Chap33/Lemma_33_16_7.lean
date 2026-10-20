/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 33.16.7: if `x : X` and `y : Y` have the same image in `S` and both canonical
residue-field maps from that image are bijective, then the relative tangent space of the
canonical point `(x, y)` of `X ×[S] Y` is canonically the direct sum of the relative tangent
spaces at `x` and `y`. The forward map is induced by the two projections, and the inverse is
induced by the fibre morphisms `1 × y` and `x × 1`. -/
@[stacks 0BEB] #check
  (AlgebraicGeometry.Scheme.Hom.pullbackTangentEquiv :
    ∀ {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y)
      (hxy : f x = g y) (hx : Function.Bijective (f.residueFieldMap x).hom)
      (hy : Function.Bijective (g.residueFieldMap y).hom),
      let xy :=
        AlgebraicGeometry.Scheme.Pullback.pointOfBaseResidueFieldMapBijective
          f g x y hxy hx hy
      -- Local instance justification (noncanonical choice): restrict the pullback tangent-space
      -- action along the explicitly supplied residue-field identifications.
      let _ : Module (X.residueField x)
          (AlgebraicGeometry.Scheme.Hom.tangentSpaceAt (pullback.fst f g ≫ f) xy) :=
        Module.compHom _
          (AlgebraicGeometry.Scheme.Pullback.pointFstResidueFieldMap
            f g x y hxy hx hy).hom
      -- Local instance justification (noncanonical choice): transport the right tangent-space
      -- action through the explicitly supplied residue-field equivalence.
      let _ : Module (X.residueField x)
          (AlgebraicGeometry.Scheme.Hom.tangentSpaceAt g y) :=
        Module.compHom _
          (AlgebraicGeometry.Scheme.Pullback.residueFieldEquivOfBaseMapBijective
            f g x y hxy hx hy).toRingHom
      AlgebraicGeometry.Scheme.Hom.tangentSpaceAt (pullback.fst f g ≫ f) xy
          ≃ₗ[X.residueField x]
        AlgebraicGeometry.Scheme.Hom.tangentSpaceAt f x ×
          AlgebraicGeometry.Scheme.Hom.tangentSpaceAt g y)

#check
  (AlgebraicGeometry.Scheme.Hom.pullbackTangentEquiv_toLinearMap :
    ∀ {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y)
      (hxy : f x = g y) (hx : Function.Bijective (f.residueFieldMap x).hom)
      (hy : Function.Bijective (g.residueFieldMap y).hom),
      let xy :=
        AlgebraicGeometry.Scheme.Pullback.pointOfBaseResidueFieldMapBijective
          f g x y hxy hx hy
      -- Local instance justification (noncanonical choice): restrict the pullback tangent-space
      -- action along the explicitly supplied residue-field identifications.
      let _ : Module (X.residueField x)
          (AlgebraicGeometry.Scheme.Hom.tangentSpaceAt (pullback.fst f g ≫ f) xy) :=
        Module.compHom _
          (AlgebraicGeometry.Scheme.Pullback.pointFstResidueFieldMap
            f g x y hxy hx hy).hom
      -- Local instance justification (noncanonical choice): transport the right tangent-space
      -- action through the explicitly supplied residue-field equivalence.
      let _ : Module (X.residueField x)
          (AlgebraicGeometry.Scheme.Hom.tangentSpaceAt g y) :=
        Module.compHom _
          (AlgebraicGeometry.Scheme.Pullback.residueFieldEquivOfBaseMapBijective
            f g x y hxy hx hy).toRingHom
      (AlgebraicGeometry.Scheme.Hom.pullbackTangentEquiv
          f g x y hxy hx hy).toLinearMap =
        AlgebraicGeometry.Scheme.Hom.pullbackTangentProjection f g x y hxy hx hy)

#check
  (AlgebraicGeometry.Scheme.Hom.pullbackTangentEquiv_symm_toLinearMap :
    ∀ {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y)
      (hxy : f x = g y) (hx : Function.Bijective (f.residueFieldMap x).hom)
      (hy : Function.Bijective (g.residueFieldMap y).hom),
      let xy :=
        AlgebraicGeometry.Scheme.Pullback.pointOfBaseResidueFieldMapBijective
          f g x y hxy hx hy
      -- Local instance justification (noncanonical choice): restrict the pullback tangent-space
      -- action along the explicitly supplied residue-field identifications.
      let _ : Module (X.residueField x)
          (AlgebraicGeometry.Scheme.Hom.tangentSpaceAt (pullback.fst f g ≫ f) xy) :=
        Module.compHom _
          (AlgebraicGeometry.Scheme.Pullback.pointFstResidueFieldMap
            f g x y hxy hx hy).hom
      -- Local instance justification (noncanonical choice): transport the right tangent-space
      -- action through the explicitly supplied residue-field equivalence.
      let _ : Module (X.residueField x)
          (AlgebraicGeometry.Scheme.Hom.tangentSpaceAt g y) :=
        Module.compHom _
          (AlgebraicGeometry.Scheme.Pullback.residueFieldEquivOfBaseMapBijective
            f g x y hxy hx hy).toRingHom
      (AlgebraicGeometry.Scheme.Hom.pullbackTangentEquiv
          f g x y hxy hx hy).symm.toLinearMap =
        AlgebraicGeometry.Scheme.Hom.pullbackTangentCopairing f g x y hxy hx hy)
