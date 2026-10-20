/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative.FlatPointClosure.GenericFlatness
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.CodimensionZero
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.flatOverInCodimensionZero

/-- An integral source has relative dimension `d` when its generic-point residue-field
transcendence degree is `d` and it carries a finite-type quasicoherent module of full support
that is flat over the base in codimension zero. -/
@[stacks 0GSK]
theorem relativeDimension_of_isIntegral {X S : Scheme.{u}}
    (f : X ⟶ S) (ℱ : X.Modules) (d : ℕ) [IsIntegral X]
    [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (htrdeg : f.residueFieldTrdegAt (genericPoint X) = d)
    (hsupport : RingedSpace.moduleSupport ℱ = Set.univ)
    (hflat : flatOverInCodimensionZero ℱ f) :
    Scheme.Hom.RelativeDimension f d := sorry

/-- If the base is irreducible, the generic fibre is dense, and all its irreducible components
have dimension `d`, then a finite-type quasicoherent module of full support that is flat over the
base in codimension zero forces the morphism to have relative dimension `d`. -/
@[stacks 0GSK]
theorem relativeDimension_of_denseGenericFiber {X S : Scheme.{u}}
    (f : X ⟶ S) (ℱ : X.Modules) (d : ℕ) [IrreducibleSpace S]
    [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (hdense : DenseRange (f.fiberι (genericPoint S)).base)
    (hdim : ∀ Z : irreducibleComponents (f.fiber (genericPoint S)),
      topologicalKrullDim Z = d)
    (hsupport : RingedSpace.moduleSupport ℱ = Set.univ)
    (hflat : flatOverInCodimensionZero ℱ f) :
    Scheme.Hom.RelativeDimension f d := sorry

end AlgebraicGeometry.Scheme.Modules.flatOverInCodimensionZero
