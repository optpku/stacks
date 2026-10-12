/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.CodimensionZero.RelativeDimension
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Modules
namespace flatOverInCodimensionZero

/- Remark 37.18.6 (1): an integral source with generic-point residue-field
transcendence degree `d` has relative dimension `d` when it carries a finite-type
quasicoherent module of full support that is flat over the base in codimension zero. -/
@[stacks 0GSK] #check
  (AlgebraicGeometry.Scheme.Modules.flatOverInCodimensionZero.relativeDimension_of_isIntegral :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) (d : ℕ) [IsIntegral X]
      [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
      (htrdeg : f.residueFieldTrdegAt (genericPoint X) = d)
      (hsupport : RingedSpace.moduleSupport ℱ = Set.univ)
      (hflat : flatOverInCodimensionZero ℱ f),
      Scheme.Hom.RelativeDimension f d)

/- Remark 37.18.6 (2): if the base is irreducible, the generic fibre is dense,
and all its irreducible components have dimension `d`, then a finite-type
quasicoherent module of full support that is flat over the base in codimension zero
forces the morphism to have relative dimension `d`. -/
@[stacks 0GSK] #check
  (AlgebraicGeometry.Scheme.Modules.flatOverInCodimensionZero.relativeDimension_of_denseGenericFiber :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) (d : ℕ) [IrreducibleSpace S]
      [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
      (hdense : DenseRange (f.fiberι (genericPoint S)).base)
      (hdim : ∀ Z : irreducibleComponents (f.fiber (genericPoint S)),
        topologicalKrullDim Z = d)
      (hsupport : RingedSpace.moduleSupport ℱ = Set.univ)
      (hflat : flatOverInCodimensionZero ℱ f),
      Scheme.Hom.RelativeDimension f d)

end flatOverInCodimensionZero
end Modules
end Scheme
end AlgebraicGeometry
