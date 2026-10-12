/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_52_8_DerivedHom
public import stacks_project.Chap76.Lemma_76_52_8_Colimit
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

/- Lemma 76.52.8: in Situation 76.52.7, the canonical cocone of derived Hom types along the
base-changed cofinal tail is a filtered colimit when `K₀` is pseudo-coherent and `L₀` has
quasi-coherent cohomology and locally finite Tor dimension as an object of
`D((X₀ ⟶ Y₀)⁻¹ 𝒪_{Y₀})`. -/
@[stacks 0DKV] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit.homDiagram_isColimit_exists :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S}
      [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsQuasiSeparated (D.obj i)]
      [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
      (s : AlgebraicSpace.Limit.QcqsAffineLimit D) (X₀ : AlgebraicSpace S)
      (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
      [Flat x₀] [FinitePresentation x₀]
      (K₀ L₀ : ModuleDerived X₀),
      IsPseudoCoherent X₀ K₀ →
        derivedQuasiCoherentModuleProperty X₀ L₀ →
          ModuleDerived.locallyFiniteTorDimensionOver x₀ L₀ →
            Nonempty (IsColimit (s.homDiagram x₀ K₀ L₀).cocone))
