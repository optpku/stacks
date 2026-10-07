module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.QcqsAffine.DerivedHom.Colimit
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Limit
namespace QcqsAffineLimit
namespace DerivedHom

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {D : OrderDual I ⥤ Scheme.{u}}
variable [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]

/- Lemma 36.29.2: for a directed inverse limit of qcqs schemes with affine transition
maps, the canonical cocone of derived Hom types is a filtered colimit when `K₀` has
quasi-coherent homology and either `E₀` is perfect or `E₀` is pseudo-coherent while
`K₀` has finite Tor dimension. -/
@[stacks 09RE] #check
  (AlgebraicGeometry.Scheme.Limit.QcqsAffineLimit.DerivedHom.diagram_isColimit :
    ∀ (s : Scheme.Limit.QcqsAffineLimit D)
      (E₀ K₀ : RingedSpace.ModuleDerived
        (D.obj (OrderDual.toDual s.base)).toRingedSpace),
      DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty
            (D.obj (OrderDual.toDual s.base)).toRingedSpace) K₀ →
        (RingedSpace.ModuleDerived.IsPerfect E₀ ∨
          (RingedSpace.ModuleDerived.IsPseudoCoherent E₀ ∧
            RingedSpace.HasFiniteTorDimension K₀)) →
          Nonempty (IsColimit (diagram s E₀ K₀).cocone))

end DerivedHom
end QcqsAffineLimit
end Limit
end Scheme
end AlgebraicGeometry
