/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.WeaklyRadicial
public import ReasLib.AlgebraicGeometry.Presheaf.Points
public import ReasLib.AlgebraicGeometry.Sheaf.ReducedInduced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.WeaklyRadicial
import StacksCheckRecall

/-!
# Weakly radicial morphisms of algebraic spaces

The fibre condition, the algebraically closed points consequence, and the
algebraic-closure base change of the absolute Galois quotient are recorded below.
The final implication is stated with the authorized surjectivity correction.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicNumbers
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient

universe u

/- Remark 76.3.5 (1): every field-valued fibre has nonempty singleton points
space and admits a monomorphism from a purely inseparable field spectrum. -/
@[stacks 049E]
#check (AlgebraicGeometry.AlgebraicSpace.WeaklyRadicial :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

/- Remark 76.3.5 (2): a surjective weakly radicial morphism is surjective on
points valued in any algebraically closed field. -/
@[stacks 049E]
#check (AlgebraicGeometry.AlgebraicSpace.WeaklyRadicial.surjectiveOnAlgClosedFieldPoints :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [WeaklyRadicial f] [Surjective f] (k : Type u) [Field k] [IsAlgClosed k]
    (σ : Spec (.of k) ⟶ S),
    Function.Surjective (fun x : ofOver (Over.mk σ) ⟶ X ↦ x ≫ f))

/- Remark 76.3.5 (3): the actual algebraic-closure base change is weakly radicial. -/
@[stacks 049E]
#check (AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.toSpec_baseChange_weaklyRadicial :
    ∀ (K : Type) [Field K] [Algebra ℚ K]
      (σ : Over.mk (FieldExtension.specMap ℚ K) ⟶ cover),
      Nonempty (SpacePresheaf.Points (toSpec_baseChange_fibre σ).obj) ∧
        Subsingleton (SpacePresheaf.Points (toSpec_baseChange_fibre σ).obj) ∧
        ∃ (L : Type) (_ : Field L) (_ : Algebra K L)
          (_ : IsPurelyInseparable K L)
          (ι : (Scheme.fppfTopology.over base).uliftYoneda.{1}.obj
                (FieldExtension.specExtend (FieldExtension.specMap ℚ K) L) ⟶
              toSpec_baseChange_fibre σ),
            Mono ι ∧
              ι ≫ pullback.snd toSpec_baseChange
                    ((Scheme.fppfTopology.over base).uliftYoneda.{1}.map σ) =
                (Scheme.fppfTopology.over base).uliftYoneda.{1}.map
                  (FieldExtension.specExtendToOver (FieldExtension.specMap ℚ K) L))

/- Remark 76.3.5 (4): the actual algebraic-closure base change remains nonradicial. -/
@[stacks 049E]
#check (AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.toSpec_baseChange_not_radicial :
    ∃ (F : Sheaf (Scheme.fppfTopology.over base) (Type 1))
      (ι : F ⟶ toSpec_baseChange_fibre (𝟙 cover)),
      FppfSheaf.IsReducedInduced ι ∧
        Nonempty (SpacePresheaf.Points F.obj) ∧
        ∀ (L : Type) [Field L] [Algebra algebraicQ L]
          [IsPurelyInseparable algebraicQ L]
          (e : F ≅ (Scheme.fppfTopology.over base).uliftYoneda.{1}.obj
            (FieldExtension.specExtend cover.hom L)),
          e.hom ≫ (Scheme.fppfTopology.over base).uliftYoneda.{1}.map
              (FieldExtension.specExtendToOver cover.hom L) ≠
            ι ≫ pullback.snd toSpec_baseChange
              ((Scheme.fppfTopology.over base).uliftYoneda.{1}.map (𝟙 cover)))

/- Remark 76.3.5 (5), correction: the source sentence needs surjectivity.
The empty morphism ∅ → Spec(ℚ) is universally injective and has property (β),
but has an empty fibre and so is not weakly radicial. Without surjectivity,
the fibrewise conclusion holds for each explicitly nonempty fibre. -/
@[stacks 049E]
#check (AlgebraicGeometry.AlgebraicSpace.isWeaklyRadicialOver.of_universallyInjective_of_propertyBeta :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [UniversallyInjective f] [PropertyBeta f] (p : FieldValuedPoint Y)
    (hne : Nonempty (Points (pullback p.hom f))),
    isWeaklyRadicialOver p.structureHom (pullback.fst p.hom f))

/- Remark 76.3.5 (5), corrected global implication: surjectivity excludes empty fibres. -/
@[stacks 049E]
#check (AlgebraicGeometry.AlgebraicSpace.WeaklyRadicial.of_universallyInjective_of_propertyBeta :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [UniversallyInjective f] [PropertyBeta f] [Surjective f], WeaklyRadicial f)
