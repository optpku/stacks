module

public import stacks_project.Chap75.Lemma_75_24_2_Colimit
public import stacks_project.Chap75.Lemma_75_24_2_DerivedHom
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit.DerivedHom

noncomputable section

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S}
variable [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsQuasiSeparated (D.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]

/- Lemma 75.24.2: in Situation 75.24.1, the canonical cocone of derived Hom types
along the cofinal tail is a filtered colimit when `K₀` has quasi-coherent cohomology
and either `E₀` is perfect or `E₀` is pseudo-coherent while `K₀` has finite Tor
dimension. -/
@[stacks 09RI] #check
  (diagram_isColimit :
    ∀ (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
      (E₀ K₀ : ModuleDerived (D.obj (OrderDual.toDual s.base))),
      derivedQuasiCoherentModuleProperty
          (D.obj (OrderDual.toDual s.base)) K₀ →
        (ModuleDerived.IsPerfect E₀ ∨
          (IsPseudoCoherent (D.obj (OrderDual.toDual s.base)) E₀ ∧
            DerivedCategory.DerivedTensor.HasFiniteTorDimension K₀)) →
          Nonempty (IsColimit (diagram s E₀ K₀).cocone))
